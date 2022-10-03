#include <unordered_set>
#include <unordered_map>
#include <iostream>
#include <string>
#include <fstream>
#include <vector>
#include <algorithm>

using namespace std;

const string label_path = "../label.csv";
const string instance_path = "../instance.txt";
const string pure_arith_path = "../pure_arith.txt";

const string origin_path = "theoryF-test/";

vector<string> m_instances;
unordered_set<string> m_pure_arith_instances;
unordered_map<string, string> m_label_map;

enum result {
    sat, unsat, memoryout, timeout, unknown
};

string res2str(result r) {
    switch(r){
        case sat:
            return "sat";
        case unsat:
            return "unsat";
        case memoryout:
            return "memoryout";
        case timeout:
            return "timeout";
        case unknown:
            return "unknown";
        default:
            return "error";
            break;
    }
}

string bool2str(bool b){
    return b ? "1" : "0";
}

class instance {
private:
    string m_str;
public:
    result m_res;
    string total_time;
    string restart;
    string learned_added;
    string learned_deleted;
    

    instance(string str): m_str(str), total_time("-"), restart("-"), learned_added("-"), learned_deleted("-")
    {}

    ~instance(){}

    std::ostream & display(std::ostream & out) const {
        out << m_str << " " << res2str(m_res) << " " << total_time << " " << restart << " " << learned_added << " " << learned_deleted << std::endl;
        return out;
    }
};

class label {
private:
    string m_str;
public:
    unsigned m_total, m_sat, m_unsat, m_solved, m_unknown, m_memoryout, m_timeout;
    label(string str): m_str(str) {
        m_total = 0; m_sat = 0; m_unsat = 0; m_solved = 0; m_unknown = 0; 
        m_memoryout = 0; m_timeout = 0;
    }

    ~label(){}

    std::ostream & display(std::ostream & out) const {
        out << m_str << " " << m_total << " " << m_sat << " " << m_unsat << " " << m_solved << 
        " "  << m_unknown << " " << m_memoryout << " " << m_timeout << std::endl;
        return out;
    }
};

unordered_map<string, instance *> m_str_instance;
unordered_map<string, label *> m_str_label;


void read_instances(){
    m_instances.clear();
    ifstream inFile(instance_path, ios::in);
    string line;
    while(getline(inFile, line)){
        m_instances.push_back(line);
    }
    inFile.close();
}

void read_pure_arith(){
    m_pure_arith_instances.clear();
    ifstream inFile(pure_arith_path, ios::in);
    string line;
    while(getline(inFile, line)){
        m_pure_arith_instances.insert(line);
    }
    inFile.close();
}

void read_labels(){
    m_label_map.clear();
    ifstream inFile(label_path, ios::in);
    string line;
    while(getline(inFile, line)){
        for(unsigned i = 0; i < line.length(); i++){
            if(line[i] == ','){
                string str1 = line.substr(0, i), str2 = line.substr(i + 1, line.length() - i - 1);
                m_label_map[str1] = str2;
                break;
            }
        }
    }
    inFile.close();
}

string get_path(string str){
    unsigned index1 = UINT_MAX, index2 = UINT_MAX;
    for(unsigned i = str.length(); i >= 0; i--){
        if(str[i] == '.' && index2 == UINT_MAX){
            index2 = i;
        }
        if(str[i] == '/'){
            index1 = i;
            break;
        }
    }
    return str.substr(index1 + 1, index2 - index1 - 1);
}

string find_number(string str){
    unsigned begin = 0, end = 0;
    for(unsigned i = 0; i < str.length(); i++){
        if(begin == 0 && str[i] >= '0' && str[i] <= '9'){
            begin = i;
        }
        else if(begin != 0 && str[i] == ' ' || str[i] == '\n' || str[i] == ')'){
            end = i - 1;
            break;
        }
    }
    return str.substr(begin, end - begin + 1);
}

void process(){
    ofstream outFile1("theoryF-test_instance.txt"), outFile2("theoryF-test_label.txt");
    unsigned unsat = 0, sat = 0, total = 0, unknown = 0, memoryout = 0, timeout = 0;
    unsigned arith_sat = 0, arith_unsat = 0, arith_solved = 0;
    unsigned bool_sat = 0, bool_unsat = 0, bool_solved = 0;
    for(auto ele: m_instances){
        total++;
        string name = get_path(ele);
        m_str_instance[name] = new instance(name);
        string path = origin_path + name + ".txt";
        ifstream inFile(path, ios::in);
        string line;
        unsigned index = 0;
        string curr_label = m_label_map[name];
        if(m_str_label.count(curr_label) == 0){
            m_str_label[curr_label] = new label(curr_label);
        }
        m_str_label[curr_label]->m_total++;
        bool is_pure_arith = m_pure_arith_instances.count(ele) > 0;

        while(getline(inFile, line)){
            if(index == 0){
                if(line.find("unsat") != string::npos){
                    unsat++;
                    m_str_instance[name]->m_res = result::unsat;
                    m_str_label[curr_label]->m_unsat++;
                    m_str_label[curr_label]->m_solved++;
                    if(is_pure_arith){
                        arith_unsat++;
                        arith_solved++;
                    }
                    else {
                        bool_unsat++;
                        bool_solved++;
                    }
                }
                else if(line.find("sat") != string::npos){
                    sat++;
                    m_str_instance[name]->m_res = result::sat;
                    m_str_label[curr_label]->m_sat++;
                    m_str_label[curr_label]->m_solved++;
                    if(is_pure_arith){
                        arith_sat++;
                        arith_solved++;
                    }
                    else {
                        bool_sat++;
                        bool_solved++;
                    }
                }
                else if(line.find("memoryout") != string::npos){
                    memoryout++;
                    m_str_instance[name]->m_res = result::memoryout;
                    m_str_label[curr_label]->m_memoryout++;
                }
                else if(line.find("timeout") != string::npos){
                    timeout++;
                    m_str_instance[name]->m_res = result::timeout;
                    m_str_label[curr_label]->m_timeout++;
                }
                else {
                    unknown++;
                    m_str_instance[name]->m_res = result::unknown;
                    m_str_label[curr_label]->m_unknown++;
                }
            }
            else {
                if(line.find("total-time") != string::npos){
                    string curr_time = find_number(line);
                    m_str_instance[name]->total_time = curr_time;
                }
                else if(line.find("nlsat-learned-added") != string::npos){
                    string curr_step = find_number(line);
                    m_str_instance[name]->learned_added = curr_step;
                }
                else if(line.find("nlsat-learned-deleted") != string::npos){
                    string curr_ratio = find_number(line);
                    m_str_instance[name]->learned_deleted = curr_ratio;
                }
                else if(line.find("nlsat-restarts") != string::npos){
                    string curr_stuck = find_number(line);
                    m_str_instance[name]->restart = curr_stuck;
                }
            }
            index ++;
        }
        inFile.close();
    }
    // std::sort(m_str_label.begin(), m_str_label.end());
    // std::sort(m_str_instance.begin(), m_str_instance.end());
    for(auto ele: m_str_instance){
        ele.second->display(outFile1);
    }
    for(auto ele: m_str_label){
        ele.second->display(outFile2);
    }
    outFile1.close();
    outFile2.close();

    std::cout << "total: " << total << std::endl;
    std::cout << "sat: " << sat << std::endl;
    std::cout << "unsat: " << unsat << std::endl;
    std::cout << "solved: " << sat + unsat << std::endl;
    std::cout << "unsolved: " << total - (sat + unsat) << std::endl;
    std::cout << "arith sat: " << arith_sat << std::endl;
    std::cout << "arith unsat: " << arith_unsat << std::endl;
    std::cout << "arith solved: " << arith_solved << std::endl;
    std::cout << "bool sat: " << bool_sat << std::endl;
    std::cout << "bool unsat: " << bool_unsat << std::endl;
    std::cout << "bool solved: " << bool_solved << std::endl;
    std::cout << "memory out: " << memoryout << std::endl;
    std::cout << "time out: " << timeout << std::endl;
    std::cout << "unknown: " << unknown << std::endl;
}

int main(){
    read_instances();
    read_pure_arith();
    read_labels();
    process();
    return 0;
}