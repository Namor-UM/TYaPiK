import itertools


class Grammar:
    non_terminals: set[str]
    terminals: set[str]
    rules: dict
    axiom: str

    def __init__(self, n: set, sigma: set, p: dict, s: str):
        self.non_terminals = n
        self.terminals = sigma
        self.rules = p
        self.axiom = s

    """
    def input_non_terminals(self, all_non_terminals: str) -> bool:
        for non_terminal in all_non_terminals:
            if ord(non_terminal) < 65 or ord(non_terminal) > 90 or non_terminal == self.axiom:
                return False
        self.non_terminals = set(all_non_terminals)
        if self.axiom not in self.non_terminals:
            self.non_terminals.add(self.axiom)
        return True

    def input_terminals(self, all_terminals: str) -> bool:
        for terminal in all_terminals:
            if ord(terminal) < 97 or ord(terminal) > 122:
                return False
        self.terminals = set(all_terminals)
        return True

    def input_rule(self, rule_data: list) -> bool:
        antecedent: str = rule_data[0]
        consequent: list = rule_data[1].split(" | ")
        if antecedent not in self.non_terminals and antecedent != self.axiom:
            return False
        for i in range(0, len(consequent)):
            if consequent[i] == "λ":
                consequent[i] = ""
            else:
                for symbol in consequent[i]:
                    if not(symbol in self.non_terminals or symbol in self.terminals or symbol == self.axiom):
                        return False
        self.rules[antecedent] = consequent
        return True

    def delete_rule_by_key(self, key: str) -> bool:
        if key in self.rules.keys():
            del self.rules[key]
            return True
        return False

    def delete_incorrect_rules(self) -> bool:
        del_result: bool = False
        for key in self.rules:
            if key not in self.non_terminals:
                del self.rules[key]
                del_result = True
            else:
                for consequent in self.rules[key]:
                    if consequent != "":
                        for symbol in consequent:
                            if not(symbol in self.non_terminals or symbol in self.terminals):
                                del self.rules[key]
                                del_result = True
        return del_result 

    def get_grammar_data(self) -> list:
        return [self.non_terminals, self.terminals, self.rules, self.axiom]
    """
    @staticmethod
    def add_new_rules_to_dict_of_p_i(dict_of_p_i: dict,
                                     dict_key: str,
                                     string: str,
                                     list_of_indexes_to_alternate: list[int]):
        amount_of_indexes = len(list_of_indexes_to_alternate)
        p_i_right_part: list[str] = []
        if amount_of_indexes > 0:
            listed_pattern: list[int]
            buffer_string: str
            index_shift: int
            combination_patterns = iter(
                itertools.product([0, 1], repeat=amount_of_indexes)
            )
            for pattern in combination_patterns:
                listed_pattern = list(pattern)
                buffer_string = string
                index_shift = 0
                for i in range(0, len(listed_pattern)):
                    if listed_pattern[i] == 0:
                        buffer_string.replace(list_of_indexes_to_alternate[i]-index_shift, "", 1)
                        index_shift += 1
                p_i_right_part.append(buffer_string)
            dict_of_p_i[dict_key] = p_i_right_part
        else:
            p_i_right_part.append(string)
            dict_of_p_i[dict_key] = p_i_right_part

    def wipe_out_excess_lambda_rules(self) -> list:
        """
        Алгоритм устранения лишних лямбда-правил!
        ---
        Некоторые понятия в комментариях могут быть Вам незнакомы.
        Это потому что я их сам придумал! Определения им даю почти сразу при употреблении.
        """
        """
        1-й шаг.
        n_lambda - все нетерминалы, из которых выводятся лямбда-цепочки.
        n_term_plus - все нетерминалы, из которых выводятся непустые терминальные цепочки.
        """
        n_lambda = set()
        n_term_plus = set()
        """
        А-й подшаг 1-го шага.
        Поиск и добавление нечистых и чистых первородных лямбда-нетерминалов. 
        Нечистые первородные лямбда-нетерминалы - нетерминалы, из которых непосредственно выводится НЕ ТОЛЬКО лямбда.
        Пример: A -> λ | a.
        Чистые первородные лямбда-нетерминалы - нетерминалы, из которых непосредственно выводится ТОЛЬКО лямбда.
        Пример: A -> λ.
        
        Чистые первородные лямбда-нетерминалы также добавим в множество pure_n_lambda. 
        Такие нетерминалы точно не окажутся в n_term_plus.
        """
        count_of_all_lambda_consequents: int
        pure_n_lambda = set()
        for non_term in self.non_terminals:
            if non_term not in self.rules.keys():
                continue
            count_of_all_lambda_consequents = self.rules[non_term].count("")
            if count_of_all_lambda_consequents > 0:
                n_lambda.add(non_term)
                if count_of_all_lambda_consequents == len(self.rules[non_term]):
                    pure_n_lambda.add(non_term)

        """
        Б-й подшаг 1-го шага.
        Поиск и добавление нечистых и чистых старшеродных лямбда-нетерминалов. 
        Нечистые старшеродные лямбда-нетерминалы - нетерминалы, из которых транзитивно выводится НЕ ТОЛЬКО лямбда.
        Пример: A -> λ | a.
        Чистые старшеродные лямбда-нетерминалы - нетерминалы, из которых транзитивно выводится ТОЛЬКО лямбда.
        Пример: A -> λ.

        Чистые старшеродные лямбда-нетерминалы также добавим в множество pure_n_lambda. 
        Такие нетерминалы точно не окажутся в n_term_plus.
        """
        while True:
            is_n_lambda_appended = False
            for non_term in self.non_terminals:
                if not(non_term in self.rules.keys() and non_term not in n_lambda):
                    continue
                count_of_all_lambda_consequents = 0
                count_of_pure_lambda_consequents = 0
                for consequent in self.rules[non_term]:
                    for symbol in consequent:
                        if symbol in n_lambda:
                            count_of_all_lambda_consequents += consequent.count(symbol)
                            if symbol in pure_n_lambda:
                                count_of_pure_lambda_consequents += consequent.count(symbol)
                    if len(consequent) == count_of_all_lambda_consequents:
                        n_lambda.add(non_term)
                        is_n_lambda_appended = True
                        if len(consequent) == count_of_pure_lambda_consequents:
                            pure_n_lambda.add(non_term)
            if not is_n_lambda_appended:
                break

        """
        В-й подшаг 1-го шага.
        Поиск и добавление нетерминалов, из которых выводятся 
        непустые терминальные цепочки, в n_term_plus.
        """
        for non_term in self.non_terminals:
            if non_term in self.rules.keys() and non_term not in pure_n_lambda:
                n_term_plus.add(non_term)

        """
        2-й шаг.
        new_rules - новый набор правил.
        """
        new_rules: dict = {}

        """
        3-й шаг.
        Найдём q - множество всех правил, в правых частях которых есть символы n_lambda
        """
        q: dict = {}

        for key in self.rules:
            is_key_added = False
            for string in self.rules[key]:
                for symbol in n_lambda:
                    if string.find(symbol) > -1:
                        q[key] = self.rules[key]
                        is_key_added = True
                        break
                if is_key_added:
                    break
            if is_key_added:
                continue

        """
        Добавим dict_of_p_i - множество правил на основе каждого i-го правила из q.
        Причём из каждого нового правила выводятся непустые цепочки
        """
        dict_of_p_i: dict = {}
        list_of_indexes_to_alternate: list[int]
        for key in q:
            for string in q[key]:
                i = 0
                list_of_indexes_to_alternate = []
                string_length = len(string)
                while i < string_length:
                    if string[i] in n_lambda and string[i] in n_term_plus:
                        list_of_indexes_to_alternate.append(i)
                        i += 1
                    elif string[i] in n_lambda:
                        string = string[:i] + string[i+1:]
                        string_length -= 1
                    else:
                        i += 1
                if len(string) > 0:
                    self.add_new_rules_to_dict_of_p_i(dict_of_p_i,
                                                      key,
                                                      string,
                                                      list_of_indexes_to_alternate)

        """
        Шаг 4.
        Добавляем в new_p все правила вида B -> a, где a не содержит символов из n_lambda
        и a != lambda.
        """
        for key in self.rules:
            if key in n_lambda:
                continue
            is_non_lambda = True
            for consequents in self.rules[key]:
                for consequent in consequents:
                    for symbol in n_lambda:
                        if consequent.find(symbol) > -1:
                            is_non_lambda = False
                            break
                    if not is_non_lambda:
                        break
                if not is_non_lambda:
                    break
            if is_non_lambda:
                new_rules[key] = self.rules[key]
        for key in dict_of_p_i:
            new_rules[key] = dict_of_p_i[key]

        """
        Шаг 5.
        Проверяем аксиому.
        Если axiom = lambda || axiom принадл. n_lambda, 
        то добавим в new_p правило new_axiom -> axiom|lambda
        """
        new_axiom: str = self.axiom
        if self.axiom == "" or self.axiom in n_lambda:
            new_axiom = "new_" + self.axiom
            new_rules[new_axiom] = [self.axiom, ""]

        """
        Шаг 6.
        Формируем новую грамматику.
        """
        print("n_lambda: {}\npure_n_lambda: {}\nn_term_plus: {}\nq: {}\ndict_of_p_i: {}".format(n_lambda,
                                                                                                pure_n_lambda,
                                                                                                n_term_plus,
                                                                                                q,
                                                                                                dict_of_p_i))

        new_non_terminals = n_term_plus
        new_non_terminals.add(new_axiom)

        new_grammar_data: list = [new_non_terminals,
                                  self.terminals,
                                  new_rules,
                                  new_axiom]

        return new_grammar_data
