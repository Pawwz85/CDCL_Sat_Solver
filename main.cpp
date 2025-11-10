#include <iostream>
#include <queue>
#include <vector>
#include <set>
#include <list>
#include <algorithm>
#include <cmath>
#include <unordered_map>
#include <climits>

#include <cstdlib> // for rand
#include <ctime>

//#define DEBUG 0
//#define BECNHMARKING 0

typedef int Literal;

class HeadAndTailList;

const double decay_factor = 0.98;
const double reset_geo_coefficient = 1.2;
const double LBD_decay_factor = 1.25;
const long initial_reset_goal = 500;

struct term_meta {
	bool value;
	int decision_level;
	double vsids_score;
	HeadAndTailList* antacement;
	std::list<HeadAndTailList*> referenced_clauses;
};

term_meta last_conflict;

// CDCL forces us to remember all variables in clauses, so we need to actually evaluate clauses
class TermAssigmentTable {

	term_meta* table = nullptr;
	size_t table_size;

	inline int clear() {
		if (table == nullptr)
			delete[] table;
	}

public:

	~TermAssigmentTable() {
		if (table) {
			delete[] table;
			table = nullptr;
		}
	}

	inline void init(unsigned int term_count) {
		table = new term_meta[term_count];
		table_size = term_count;

		for (int i = 0; i < term_count; ++i) {
			table[i].antacement = nullptr;
			table[i].decision_level = -1;
			table[i].value = false;
			table[i].vsids_score = 0;
			table[i].referenced_clauses = std::list<HeadAndTailList*>();
		}
	}

	// returns true if and only if given literal is satisfied
	inline bool is_lit_satisfied(int lit) {
		int index = abs(lit) - 1;
		return table[index].decision_level != -1 && ((lit > 0) == table[index].value);
	}

	term_meta& get_term_by_lit(int lit) {
		int index = abs(lit) - 1;
		return table[index];
	}

	int VSIDS() {
		double result_score = -1;
		double local_score;
		int result = 1;

		for (int i = 0; i < table_size; ++i) {
			if (table[i].decision_level == -1 && table[i].vsids_score > result_score) {
				result_score = table[i].vsids_score;
				result = i + 1;
			}
		}

		return result;
	}

	void update_vsids() {
		for (int i = 0; i < table_size; ++i) {
			table[i].vsids_score *= decay_factor;
		}
	}

	size_t get_term_count() {
		return table_size;
	}
};

TermAssigmentTable term_table;

enum clause_status {
	UNRESOLVED,
	UNIT,
	UNSATISFIED,
	SATISFIED
};


struct HeadAndTailList_snapshot {
	void* head;
	void* tail;
};

class HeadAndTailList {
	int* literals;
	int* head;
	int* tail;

	term_meta* head_meta;
	term_meta* tail_meta;

	std::list<HeadAndTailList*>::iterator head_it;
	std::list<HeadAndTailList*>::iterator tail_it;

	int size;

	void ref(int*& watcher, term_meta*& meta, std::list<HeadAndTailList*>::iterator& it) {
		meta->referenced_clauses.erase(it);
		meta = &term_table.get_term_by_lit(*watcher);
		meta->referenced_clauses.push_front(this);
		it = meta->referenced_clauses.begin();
	}

	bool resolve_watcher(int*& watcher, int* const& other, term_meta*& meta, std::list<HeadAndTailList*>::iterator& it) {
		int* org_pos = watcher;
		for (watcher = watcher + 1; watcher != end(); ++watcher) {
			if ((!term_table.is_lit_satisfied(-*watcher) && (watcher != other))) {
				ref(watcher, meta, it);
				return true;
			}

		}

		for (watcher = begin(); watcher != org_pos; ++watcher) {
			if ((!term_table.is_lit_satisfied(-*watcher) && (watcher != other))) {
				ref(watcher, meta, it);
				return true;
			}
		}

		return false;
	}

	inline bool meta_has_assigned_value(term_meta* const& meta, bool value) {
		if (meta->decision_level == -1) return false;
		return meta->value == value;
	}

	clause_status calculate_status() {
		bool hpolar = *head > 0, tpolar = *tail > 0;
		if (meta_has_assigned_value(head_meta, hpolar) || meta_has_assigned_value(tail_meta, tpolar))
			return SATISFIED;

		bool hsat, tsat;
		hsat = meta_has_assigned_value(head_meta, !hpolar);
		tsat = meta_has_assigned_value(tail_meta, !tpolar);
		if (hsat && tsat)
			return UNSATISFIED;

		return ((hsat != tsat) || head == tail) ? UNIT : UNRESOLVED;
	}


public:

	HeadAndTailList() {
		size = 0;
		literals = nullptr;
	}

	~HeadAndTailList() {
		if (size) delete[] literals;
	}

	void reserve(size_t size) {
		if (literals) delete[] literals;
		this->size = size;
		this->literals = new int[size];
		this->head = literals;
		this->tail = this->head + size - 1;
	}

	bool assign(int assigned_term) {
		bool anyChange = false;


#ifdef DEBUG
		char d;
		if (assigned_term <= 0) {
			std::cout << "Assertion failed, term is negative\n";
			std::cin >> d;
		}
#endif // DEBUG

		if (*head == assigned_term || *head == -assigned_term)
			anyChange = resolve_watcher(head, tail, head_meta, head_it);



		if (*tail == assigned_term || *tail == -assigned_term)
			anyChange = resolve_watcher(tail, head, tail_meta, tail_it);

		return anyChange;
	}

	clause_status get_status() {
		return calculate_status();
	}

	bool calculate_references() {
		head_meta = &term_table.get_term_by_lit(*head);
		head_meta->referenced_clauses.push_front(this);
		head_it = head_meta->referenced_clauses.begin();

		tail_meta = &term_table.get_term_by_lit(*tail);
		tail_meta->referenced_clauses.push_front(this);
		tail_it = tail_meta->referenced_clauses.begin();
		return true;
	}

	void get_snapshot(HeadAndTailList_snapshot& snapshot) {
		snapshot.head = head;
		snapshot.tail = tail;
	}

	void recover_from_snapshot(HeadAndTailList_snapshot& snapshot) {
		this->head = (int*)snapshot.head;
		this->tail = (int*)snapshot.tail;
	}

	int getUnitValue() {
		return (term_table.is_lit_satisfied(-*head)) ? *tail : *head;
	}

	// iterator for all literals
	int* begin() { return literals; };
	int* end() { return literals + size; };

	// used for checking if reference got updated
	int* getHead() { return head; }
	int* getTail() { return tail; }
};

typedef HeadAndTailList* Clause;

struct term_trail_record {
	int decision_level; // decision level on which term was decided
	bool value; // value assigned to this term
	Clause antecent; // clause with caused this term to be resolved
};


HeadAndTailList* learn_clause(term_meta& conflict_meta) {
	int decision_level = conflict_meta.decision_level;
	size_t LBD;
	std::list<int> learned_clause;
	std::set<int> tmp_set;
	for (int* p = conflict_meta.antacement->begin(); p != conflict_meta.antacement->end(); ++p)
		learned_clause.push_back(*p);


	bool anyChange;
	bool literal_found;

	Literal temp;
	size_t counter;

	do {
		anyChange = false;
		literal_found = false;
		counter = 0;

		for (int p : learned_clause) {
			term_meta& meta = term_table.get_term_by_lit(p);
			if ((meta.decision_level == decision_level)) {
				if (meta.antacement != nullptr) {
					temp = p;
					literal_found = true;
				}

				++counter;
			}
		}

		if (counter > 1 && literal_found) {

			anyChange = true;
			term_meta& meta = term_table.get_term_by_lit(temp);
			tmp_set.clear();

			int head = *meta.antacement->getHead();
			int tail = *meta.antacement->getTail();

			for (int* p = meta.antacement->begin(); p != meta.antacement->end(); ++p) {
				//if (term_table.get_term_by_lit(*p).decision_level  decision_level)
				tmp_set.insert(*p);
			}

			for (int lit : learned_clause)
				if (tmp_set.find(-lit) != tmp_set.end() || lit == temp)
					tmp_set.erase(-lit);
				else
					tmp_set.insert(lit);

			learned_clause.clear();

			for (int lit : tmp_set)
				learned_clause.push_back(lit);
		}

	} while (anyChange);
	tmp_set.clear();

	int dec_lvl;
	for (int lit : learned_clause) {
		dec_lvl = term_table.get_term_by_lit(lit).decision_level;
		if (dec_lvl > 0) tmp_set.insert(dec_lvl);
	}

	LBD = tmp_set.size();

	HeadAndTailList* result = new HeadAndTailList();
	result->reserve(learned_clause.size());

	int* p = result->begin();

	for (int lit : learned_clause) {
		term_table.get_term_by_lit(lit).vsids_score += pow(LBD_decay_factor, -(float)LBD);
		*p = lit;
		++p;
	}


	result->calculate_references();
	term_table.update_vsids();
	return result;

}

int debug_branch_id = 0;


float clause_complexity(int size) {
	//return size;
	return log2f(powf(2., size) - 1) - size;

}


struct decision_level_snapshot {
	int decision_level;
	int chosen_term;
	int visit_count;
	bool choosen_value;
	std::unordered_map<Clause, HeadAndTailList_snapshot> clause_snapshots;
	std::set<int> used_terms;
	std::list<Clause> satisfied_clauses;
};

int find_backjump_level(Clause learned_clause) {
	int result = INT_MAX;
	int l;
	for (int* p = learned_clause->begin(); p != learned_clause->end(); ++p) {
		l = term_table.get_term_by_lit(*p).decision_level;

#ifdef DEBUG
		std::cout << "lit: " << *p << ", decision lvl: " << l << "\n";
#endif // DEBUG

		result = (l < result && l > 0) ? l : result;
	}

	return (result == INT_MAX) ? -1 : result;
}

struct unit_report_form {
	Clause unit;
	Clause antacement;
};

inline void substitute(int term, int decision_level, std::set<int>& free_terms, decision_level_snapshot& snapshot, std::queue<unit_report_form>& unit_clauses) {

	free_terms.erase(term);
	snapshot.used_terms.insert(term);
	term_meta* term_meta_;

	int lit;

	static std::vector<Clause> clone;
	clone.reserve(term_table.get_term_by_lit(term).referenced_clauses.size());
	std::vector<Clause>::iterator it = clone.begin();


	clone.insert(clone.begin(), term_table.get_term_by_lit(term).referenced_clauses.begin(), term_table.get_term_by_lit(term).referenced_clauses.end());

	Clause c;
	for (it = clone.begin(); it != clone.end(); it++) {
		c = *it;

		c->assign(term);
		clause_status status = c->get_status();
		switch (status) {
		case UNIT:
			lit = c->getUnitValue();
			//std::cout << "Unit, lit: "<< lit <<"\n";
			term_meta_ = &term_table.get_term_by_lit(lit);
			if (term_meta_->decision_level == -1) {
				unit_clauses.push({ c, c });
			}
			break;

		case UNSATISFIED:
			//			std::cout << "Unsat, antacement:  "<< c << "\n";
			last_conflict.antacement = c;
			last_conflict.decision_level = decision_level;
			unit_clauses.push({ c, c });
			break;
		case SATISFIED:
			break;
		}
	}
	clone.clear();
}

inline bool unit_propagation(int decision_level, std::set<int>& free_terms, decision_level_snapshot& snapshot, std::queue<unit_report_form>& units) {
	int term;
	int lit;
	bool conflict_found = false;
	unit_report_form form;
	Clause current_clause;

	while (!units.empty()) {
		form = units.front();
		current_clause = form.unit;
		units.pop();
		switch (current_clause->get_status()) {
		case UNIT:
			lit = current_clause->getUnitValue();
			term = abs(lit);
			term_table.get_term_by_lit(lit).decision_level = decision_level;
			term_table.get_term_by_lit(lit).antacement = current_clause;
			term_table.get_term_by_lit(lit).value = lit > 0;
			substitute(term, decision_level, free_terms, snapshot, units);


			break;

		case UNSATISFIED:
			conflict_found = true;
			//std::cout << "Unsat lit, antacement:  " << form.antacement << "\n";
			last_conflict.antacement = current_clause;
			last_conflict.decision_level = decision_level;

			while (!units.empty()) units.pop();
			goto PROCEDURE_RETURN;
		}

	}

PROCEDURE_RETURN:
	return conflict_found;
}

void backtrack(int& decision_level, int backjmp_lvl, std::set<int>& free_terms, std::vector<decision_level_snapshot>& snapshots) {

	while (decision_level >= backjmp_lvl) {
		decision_level_snapshot* current_snapshot;
		current_snapshot = &snapshots[decision_level - 1];

		for (int term : current_snapshot->used_terms) {
			free_terms.insert(term);
			term_table.get_term_by_lit(term).decision_level = -1;
			term_table.get_term_by_lit(term).antacement = nullptr;
		}

		current_snapshot->satisfied_clauses.clear();
		current_snapshot->used_terms.clear();
		current_snapshot->clause_snapshots.clear();
		--decision_level;
		//snapshots.pop_back();
		// TODO: learned cause might cause another unit propagation cascade
	}

	last_conflict.decision_level = -1;
	last_conflict.antacement = nullptr;
}


bool solve_sat(std::set<int>& free_terms, std::list<Clause>& formula) {

	long restart_goal = initial_reset_goal;
	long restart_counter = 0;


	std::queue<unit_report_form> units;

	if (formula.size() == 0)
		return true;


	std::vector<decision_level_snapshot> snapshots;


	decision_level_snapshot initial_state;
	initial_state.decision_level = 0;

	bool tried_value = true;

	for (Clause c : formula)
		if (c->get_status() == UNIT)
			units.push({ c, nullptr });


	if (unit_propagation(0, free_terms, initial_state, units))
		return false;

	int decision_level = 0;

	decision_level_snapshot* current_snapshot;

	while (free_terms.size()) {

		decision_level++;
		if (decision_level > snapshots.size())
			snapshots.push_back({});
		current_snapshot = &snapshots[decision_level - 1];
		current_snapshot->decision_level = decision_level;

		int term = term_table.VSIDS();
		bool chosen_value;
		chosen_value = term_table.get_term_by_lit(term).value; // cached value from previous decision / unit propagation
		// TODO: check if the chosen term


		term_table.get_term_by_lit(term).value = chosen_value;
		term_table.get_term_by_lit(term).antacement = nullptr;
		term_table.get_term_by_lit(term).decision_level = decision_level;

		current_snapshot->chosen_term = term;
		current_snapshot->choosen_value = chosen_value;
#ifdef DEBUG
		std::cout << "Decision level: " << decision_level << ", Chosen term: " << term << ", value: " << current_snapshot->choosen_value << "\n";
#endif // DEBUG

		substitute(term, decision_level, free_terms, *current_snapshot, units);
		while (unit_propagation(decision_level, free_terms, *current_snapshot, units)) {

			if (last_conflict.antacement == nullptr) {
				return false;
			}

			Clause learned_clause = learn_clause(last_conflict);

			int backjmp_lvl = find_backjump_level(learned_clause);


#ifdef DEBUG
			std::cout << "Decision lvl: " << decision_level << ", Backjmp lvl: " << backjmp_lvl << ", chosen term: " << current_snapshot->chosen_term << ", value: " << chosen_value << "\n"; "\n";
#endif // DEBUG


			if (backjmp_lvl <= 0)
				return false;

			if (backjmp_lvl == 1) {
				restart_counter = 0;
			}
			else	if (restart_counter == restart_goal) {
				backjmp_lvl = 1;
				restart_counter = 0;
				restart_goal *= reset_geo_coefficient;
			}
			++restart_counter;


			backtrack(decision_level, backjmp_lvl, free_terms, snapshots);

			formula.push_back(learned_clause);



			if (learned_clause->get_status() == UNIT) {
				// unit learned, do reset to level 1

				backtrack(decision_level, 1, free_terms, snapshots);
				units.push({ learned_clause, learned_clause });
				//std::cout << "Unit learn, reset: "<< decision_level <<"\n";
				if (unit_propagation(0, free_terms, initial_state, units)) {




					return false;
				}

			}


			//	std::cout << "Learned clause status: " << learned_clause->get_status() << "\n";
		}
	}

	return true;
}

void testcase() {
	int term_count;
	int clause_count;

	std::cin >> term_count >> clause_count;

	term_table.init(term_count);

	std::list<int> temp;
	Clause tmp_clause;
	std::list<Clause> formula;

	int literal;
	std::set<int> terms;

	for (int i = 1; i <= term_count; ++i) {
		terms.insert(i);
		// randomize search
		//term_table.get_term_by_lit(i).vsids_score += rand() / double(RAND_MAX);
	}

	for (int i = 0; i < clause_count; ++i) {

		temp.clear();
		do {
			std::cin >> literal;
			if (literal) temp.push_back(literal);

		} while (literal);

		tmp_clause = new HeadAndTailList;
		tmp_clause->reserve(temp.size());

		int* p = tmp_clause->getHead();
		for (int lit : temp) {
			term_table.get_term_by_lit(lit).vsids_score += 1.f/temp.size();
			*p = lit;
			++p;
		}

		tmp_clause->calculate_references();

		formula.push_back(tmp_clause);
	}

	term_table.update_vsids();


	




	bool result = solve_sat(terms, formula);
	std::cout << ((result) ? "TAK" : "NIE") << "\n";

#ifdef DEBUG
	std::cout << "\n";
	for (int i = 1; i <= term_count; ++i)
		std::cout << "Term " << i << " value is: " << term_table.get_term_by_lit(i).value << "\n";

#endif // DEBUG

	for (int i = 1; i <= term_count; ++i)
		term_table.get_term_by_lit(i).referenced_clauses.clear();


	for (Clause c : formula) {
		delete c;
	}

	formula.clear();

}

int main() {
	srand(time(0));
	std::ios_base::sync_with_stdio(false);
	std::cin.tie(NULL);
	int n = 1;

#ifndef BECNHMARKING
	std::cin >> n;
#endif // !BECNHMARKING



	for (int i = 0; i < n; ++i)
		testcase();
}