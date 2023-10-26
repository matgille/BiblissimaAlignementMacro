import copy
import glob
import json
import random
import string
import traceback
import datetime

import collatex

import lxml.etree as ET


# L'ordre es différents alignements est manuel. Voyons un cas précis
# Dans Z on a toute la partie 3. C'est sur quoi on va travailler.

def test_file_writing(object, name, format):
    with open(f"/home/mgl/Documents/{name}", "w") as output_file:
        if format == "json":
            json.dump(object, output_file)


def generateur_id(size=6, chars=string.ascii_uppercase + string.ascii_lowercase + string.digits) -> str:
    random_string = ''.join(random.choice(chars) for _ in range(size))
    return random_string


def log_stamp():
    with open("logs/errors.txt", "a") as log_file:
        log_file.write("\n\n --- \n\n")
        log_file.write(f"New attempt -- {datetime.datetime.now()}")
        log_file.write("\n")


def write_log(message):
    with open("logs/errors.txt", "a") as log_file:
        log_file.write(f"{message}\n")


def print_unaligned_sents(aligned_table: list):
    try:
        wit_a_sent = " ".join([wit_a['t'] if wit_a else "" for wit_a, _ in aligned_table])
        wit_a_sent = wit_a_sent.replace(" .", ".").replace(" ,", ",")
        wit_b_sent = " ".join([wit_b['t'] if wit_b else "" for wit_a, wit_b in aligned_table])
        wit_b_sent = wit_b_sent.replace(" .", ".").replace(" ,", ",")
        wit_a_ids = " ".join([wit_a['xml:id'] if wit_a else "" for wit_a, _ in aligned_table])
        wit_b_ids = " ".join([wit_b['xml:id'] if wit_b else "" for _, wit_b in aligned_table])
        print("Unalined sentences:")
        print(f"{wit_a_sent}\n{wit_a_ids}\n{wit_b_sent}\n{wit_b_ids}")
    except Exception:
        print(traceback.format_exc())


def print_aligned_sents(aligned_table: list, index):
    try:
        wit_a_sent = " ".join([wit_a['t'] if wit_a else "" for wit_a, _ in aligned_table[index - 10:index + 10]])
        wit_a_sent = wit_a_sent.replace(" .", ".").replace(" ,", ",")
        wit_b_sent = " ".join(
            [wit_b['t'] if wit_b else "" for wit_a, wit_b in aligned_table[index - 10:index + 10]])
        wit_b_sent = wit_b_sent.replace(" .", ".").replace(" ,", ",")
        print("Aligned sentences:")
        print(f"{wit_a_sent}\n{wit_b_sent}")
    except Exception:
        print(traceback.format_exc())


def check_if_match(json_table: str, target_id: str) -> (bool, str):
    json_table = json.loads(json_table)
    with open("/home/mgl/Documents/test/json_table.json", "w") as output_table:
        json.dump(json_table, output_table)
    # On produit l'alignement un à un
    aligned_table = list(zip([token[0] if token else None for token in json_table['table'][0]],
                             [token[0] if token else None for token in json_table['table'][1]]))
    test_file_writing(object=aligned_table, name="aligned.json", format="json")
    with open("/home/mgl/Documents/test/json_aligned_table.json", "w") as output_table:
        json.dump(aligned_table, output_table)

    # Ici on ne va chercher que le pivot, ce qui n'est pas suffisant parfois (cas de la ponctuation). Il
    # Faudrait trouver une méthode avec plus de contexte.
    print(f"Searching for {target_id} element")
    for index, (base_witness, target_witness) in enumerate(aligned_table):
        if base_witness and target_witness:
            # Ici il manque le cas où la cible est vide.
            if base_witness['xml:id'] == target_id:
                print("Found target")
                print(base_witness)
                print(target_witness)
                if base_witness['t'] == target_witness['t']:
                    print_aligned_sents(aligned_table=aligned_table, index=index)
                    print(f"Division should start after {target_witness['xml:id']}")
                    # Ici il faut ajouter une condition sur le noeud suivant: si c'est un tei:pc, on l'inclut.
                    return True, target_witness['xml:id']
                elif aligned_table[index - 1][0]['t'] == aligned_table[index - 1][1]['t']:
                    print_aligned_sents(aligned_table=aligned_table, index=index - 1)
                    print("Previous token match !")
                    print(f"Division should start after {target_witness['xml:id']}")
                    return True, aligned_table[index - 1][1]['xml:id']
        elif base_witness and not target_witness:
            # On va chercher plus haut
            if base_witness['xml:id'] == target_id:
                if aligned_table[index - 1][0]['t'] == aligned_table[index - 1][1]['t']:
                    print_aligned_sents(aligned_table=aligned_table, index=index - 1)
                    print("Previous token match !")
                    return True, aligned_table[index - 1][1]['xml:id']

    # Si on arrive ici, c'est que quelque chose s'est mal passé.
    print("Something went wrong.")
    print_unaligned_sents(aligned_table=aligned_table)


def write_tree(path, tree):
    print(f"Writing file to {path}")
    with open(path, "w") as output_file:
        output_file.write(ET.tostring(tree, pretty_print=True).decode('utf8'))


class Aligner:
    def __init__(self, target_path: str, source_file: str):
        # On parse chaque fichier
        self.tei_ns = 'http://www.tei-c.org/ns/1.0'
        self.ns_decl = {'tei': self.tei_ns}
        self.source_file = ET.parse(source_file)
        self.source_file_id = source_file.split("/")[-1].replace(".xml", "")
        target_files = glob.glob(target_path)
        self.dict_of_parsed_files = {}
        self.treated_node_names = []
        log_stamp()
        for file in target_files:
            self.dict_of_parsed_files[file.split("/")[-1].replace(".xml", "")] = ET.parse(file)

        # On crée les arbres de sortie à partir des arbres d'entrée
        self.output_tree = {key: copy.deepcopy(tree) for key, tree in self.dict_of_parsed_files.items()}

        self.target_tokens, self.target_ids, self.tokens_and_ids = dict(), dict(), dict()

        # print("Retrieving tokens for each document")
        # for basename, target_file in self.dict_of_parsed_files.items():
        #     print(basename)
        #     self.target_tokens[basename] = target_file.xpath("descendant::node()[self::tei:w or self::tei:pc]/@lemma",
        #                                                      namespaces=self.ns_decl)
        #     self.target_ids[basename] = target_file.xpath("descendant::node()[self::tei:w or self::tei:pc]/@xml:id",
        #                                                   namespaces=self.ns_decl)
        #     self.tokens_and_ids[basename] = list(zip(self.target_tokens[basename], self.target_ids[basename]))
        #
        # self.words_and_pc = dict()
        # for basename, target_file in self.output_tree.items():
        #     self.words_and_pc[basename] = target_file.xpath("descendant::node()[self::tei:pc or self::tei:w]",
        #                                                     namespaces=self.ns_decl)
        #
        # self.all_nodes = dict()
        # for basename, target_file in self.output_tree.items():
        #     self.all_nodes[basename] = target_file.xpath("descendant::tei:div[@type='partie']/descendant::node()",
        #                                                  namespaces=self.ns_decl)

    def structure_tree(self, elements: list, ids: list, context, index_context, key):
        elements_and_ids = list(zip(elements, ids))
        print(elements_and_ids)
        context_target_nodes = self.output_tree[key].xpath(context, namespaces=self.ns_decl)[index_context]
        all_nodes = context_target_nodes.xpath(f"descendant::node()[not(self::text())]", namespaces=self.ns_decl)
        all_ids = context_target_nodes.xpath(
            f"descendant::node()[not(self::text())]/@*[name()='n' or name()='xml:id']", namespaces=self.ns_decl)
        nodes_and_ids = list(zip(all_nodes, all_ids))
        for index, (element, (min_id, max_id)) in enumerate(elements_and_ids):
            element_name = element.xpath("name()")
            # On récupère les attributs sous la forme d'un dictionnaire
            attributes = element.attrib
            print(element_name)
            # Va savoir pourquoi mais l'argument nsmap ne fonctionne pas ici.
            element_to_insert = ET.Element("{" + self.tei_ns + "}" + element_name)
            for attribute, value in attributes.items():
                element_to_insert.set(attribute, value)
            # On fonctionne différemment pour le premier élément de la liste
            if index != 0:
                following_anchor = \
                    [nodes_and_ids[index + 1][0] for index, (node, ident) in enumerate(nodes_and_ids) if
                     ident == min_id][0]
                following_anchor.addprevious(element_to_insert)
                print(f"Placing anchor before element {following_anchor.xpath('@xml:id')}")
            else:
                following_anchor = [node for index, (node, ident) in enumerate(nodes_and_ids) if ident == min_id][0]
                following_anchor.addprevious(element_to_insert)
                print(f"Placing anchor before element {following_anchor.xpath('@xml:id')}")
            [write_tree(f"/home/mgl/Documents/test/{basename}_{element_name}_intermed_{index}.xml",
                        self.output_tree[basename])
             for basename in self.output_tree.keys()]
            context_target_nodes = self.output_tree[key].xpath(context, namespaces=self.ns_decl)[index_context]
            all_nodes = context_target_nodes.xpath(f"child::node()[not(self::text())]", namespaces=self.ns_decl)
            print(f"Minimal range id: {min_id} | Maximal range id: {max_id}")
            for idx, node in enumerate(all_nodes):
                if index == 0:
                    if len(node.xpath("@xml:id")) > 0:
                        if node.xpath("@xml:id")[0] == min_id:
                            min_position_in_full_list = idx
                            print(f"Minimal pos found for first loop: {min_position_in_full_list}")
                    else:
                        continue
                else:
                    if len(node.xpath("@xml:id")) > 0:
                        if node.xpath("@xml:id")[0] == following_anchor.xpath("@xml:id")[0]:
                            print("Minimal pos found")
                            min_position_in_full_list = idx
                    else:
                        continue
                if node.xpath("@xml:id")[0] == max_id:
                    print("Maximal pos found")
                    max_position_in_full_list = idx
            print(following_anchor.xpath("@xml:id"))
            print(f"Positions: {min_position_in_full_list} and {max_position_in_full_list}")
            print(f"Index: {index}")
            if index == 0:
                items_to_shift = all_nodes[min_position_in_full_list: max_position_in_full_list + 1]
            else:
                items_to_shift = all_nodes[min_position_in_full_list: max_position_in_full_list + 1]
            for word in items_to_shift:
                try:
                    element_to_insert.append(word)
                except ValueError:
                    print(traceback.format_exc())
                    print(word)

        print("Done !")

    def align(self, query, context, proportion):
        for target_document in self.output_tree.keys():
            print(f"Trying to align {target_document} on {query} with {context} context.")
            # On veut d'abord aligner les chapitres
            # Puis les titres de chapitre
            # Puis les divisions.
            # On a donc besoin d'une fonction d'alignement avec un XPATH.
            # Première requête: "//tei:div[@type='chapitre']"
            # On va itérer sur chaque division
            # On prend le nombre de mots de la division source,
            # et on va chercher dans cette zone à aligner la source et la cible
            # Pour la première division c'est facile
            # Pour la suite, il faut mettre à jour la zone en fonction de la longueur de la division de la cible
            # Point faible de cette méthode: ça fonctionne de manière incrémentielle,
            # et si ça bloque quelque part, le processus complet est bloqué.
            # Il faudra probablement recourir à une méthode de text reuse en complément.
            # TODO: Bien penser à passer à des boucles pour gérer + de deux textes OU recommencer sur un texte nouveau à chaque fois.
            context_source_nodes = self.source_file.xpath(context, namespaces=self.ns_decl)
            context_target_nodes = self.output_tree[target_document].xpath(context, namespaces=self.ns_decl)
            for index_context, (context_source_node, context_target_node) in enumerate(
                    list(zip(context_source_nodes, context_target_nodes))):
                structure_source_elements = context_source_node.xpath(query, namespaces=self.ns_decl)

                # On ajoute des identifiants aux éléments qui en sont dépourvus
                unidentified_elements = [element for element in
                                         context_target_node.xpath(
                                             "descendant::node()[not(self::text() or self::comment())]")
                                         if len(element.xpath("@n")) == 0 and len(element.xpath("@xml:id")) == 0]
                for element in unidentified_elements:
                    try:
                        element.set("n", generateur_id())
                    except TypeError:
                        print(traceback.format_exc())
                        print(element.type)
                        exit(0)

                target_tokens = context_target_node.xpath("descendant::node()[self::tei:w or self::tei:pc]",
                                                          namespaces=self.ns_decl)
                target_lemmas = context_target_node.xpath("descendant::node()[self::tei:w or self::tei:pc]/@lemma",
                                                          namespaces=self.ns_decl)
                assert len(target_lemmas) == len(target_tokens), "Merci de vérifier que le corpus cible est lemmatisé"
                target_ids = context_target_node.xpath("descendant::node()[self::tei:w or self::tei:pc]/@xml:id",
                                                       namespaces=self.ns_decl)
                target_tokens_ids = list(zip(target_tokens, target_ids))
                current_source_position = 0
                current_target_position = 0
                source_lemmas = context_source_node.xpath("descendant::node()[self::tei:w or self::tei:pc]/@lemma",
                                                          namespaces=self.ns_decl)
                source_ids = context_source_node.xpath("descendant::node()[self::tei:w or self::tei:pc]/@xml:id",
                                                       namespaces=self.ns_decl)
                assert len(source_ids) == len(source_lemmas), "Merci de vérifier que le corpus source est lemmatisé"

                source_lemmas_ids = list(zip(source_lemmas, source_ids))
                target_positions = [0, ]
                target_id_list = [target_ids[0], ]
                for index, division in enumerate(structure_source_elements):

                    # On a besoin de l'identifiant de fin de la division courante du
                    # document source. On va
                    # ensuite regarder si ce token est dans la table alignée, pour identifier
                    # la fin de la division du document cible.
                    try:
                        last_token_current_div = division.xpath(
                            "descendant::node()[self::tei:w or self::tei:pc][last()]/@xml:id", namespaces=self.ns_decl)[
                            0]
                    except IndexError:
                        print(traceback.format_exc())
                        print(ET.tostring(division))
                        exit(0)
                    source_lemmas_per_div = division.xpath("descendant::node()[self::tei:w or self::tei:pc]/@lemma",
                                                           namespaces=self.ns_decl)
                    number_of_tokens_in_div = len(source_lemmas_per_div)
                    tokens_fraction = round(number_of_tokens_in_div * proportion)
                    current_source_position += number_of_tokens_in_div
                    source_search_range = [max(0, current_source_position - tokens_fraction),
                                           current_source_position + tokens_fraction]
                    if index == 0:
                        current_target_position = number_of_tokens_in_div
                    else:
                        current_target_position += number_of_tokens_in_div
                    target_search_range = [max(0, current_target_position - tokens_fraction),
                                           current_target_position + tokens_fraction]
                    print(current_target_position)
                    print(f"Source search range: {source_search_range}")
                    print(f"Target search range: {target_search_range}")
                    source_tokens_to_compare = source_lemmas_ids[source_search_range[0]: source_search_range[1]]
                    source_list = [{"t": lemma, "xml:id": id} for lemma, id in source_tokens_to_compare]
                    collatex_dict = {"witnesses": [{"id": f"{self.source_file_id}", "tokens": source_list}]}
                    # for basename, target_file in self.dict_of_parsed_files.items():
                    zip_target_token_id = list(zip(target_lemmas, target_ids))
                    if index == 0:
                        target_tokens_to_compare = zip_target_token_id[
                                                   source_search_range[0]: source_search_range[1]]
                    else:
                        target_tokens_to_compare = zip_target_token_id[
                                                   target_search_range[0]: target_search_range[1]]
                    target_list = [{"t": lemma, "xml:id": id} for lemma, id in target_tokens_to_compare]
                    collatex_dict["witnesses"].append({"id": target_document, "tokens": target_list})
                    print("Collating")
                    try:
                        collation_table = collatex.collate(collation=collatex_dict, output="json", segmentation=False)
                    except AssertionError:
                        print(f"Error with query {query} and context {context}")
                        print(traceback.format_exc())
                        print(f"Collatex dict: {collatex_dict}")
                        continue
                    except KeyError:
                        print(f"Error with query {query} and context {context}")
                        print(traceback.format_exc())
                        continue
                    try:
                        match, matching_id = check_if_match(json_table=collation_table,
                                                            target_id=last_token_current_div)
                        print(f"Div {index + 1} aligned.")
                        print(matching_id)
                        current_target_position = \
                            [index for index, (token, id) in enumerate(target_tokens_ids) if id == matching_id][
                                0]
                        current_target_id = \
                            [id for (token, id) in target_tokens_ids if id == matching_id][0]
                        print(current_target_id)
                        print(f"Current position: {current_target_position}")
                        target_positions.append(current_target_position)
                        target_id_list.append(current_target_id)

                    except Exception:
                        print(traceback.format_exc())
                        print(last_token_current_div)
                        print(f"Unable to align div {index + 1}. Please check structure in source document.")
                        division_attributes = division.attrib
                        write_log(
                            f"Alignment error for target file {target_document}: division {','.join(attribute for attribute in division_attributes.values())}")
                        # collation_table = collatex.collate(collation=collatex_dict, output="csv", segmentation=False)
                        # with open(f"/home/mgl/Documents/tsv_{index + 2}.tsv", "w") as output_file:
                        #     output_file.write(collation_table)
                        break
                target_id_list = [(target_id_list[index], target_id_list[index + 1]) for index, _
                                  in enumerate(target_id_list[:len(target_id_list) - 1])]
                print("Structuring tree:")
                try:
                    self.structure_tree(elements=structure_source_elements,
                                        ids=target_id_list, context=context,
                                        index_context=index_context, key=target_document)
                except Exception:
                    traceback.print_exc()
                    exit(0)
                [write_tree(f"/home/mgl/Documents/test/{basename}.xml", self.output_tree[basename])
                 for basename in self.output_tree.keys()]


if __name__ == '__main__':
    # Le contexte pour boucler
    context_query_1 = "//tei:div[@type='partie']"
    # La requête à effectuer
    example_query_1 = "//tei:div[@type='chapitre']"

    # On va chercher tous les éléments au même niveau de hiérarchie, sinon ça ne marche pas
    context_query_2 = "//tei:div[@type='chapitre']"
    example_query_2 = "descendant::node()[self::tei:head or self::tei:div]"

    aligner = Aligner(
        target_path="/home/mgl/Bureau/Travail/projets/alignement/alignement_global_unilingue/data/transform/*.xml",
        source_file="/home/mgl/Bureau/Travail/projets/alignement/alignement_global_unilingue/data/Source"
                  "/Sal_J.xml")

    # aligner = Aligner(target_path="/home/mgl/Documents/Mad_A.xml",
    #                   source_file="/home/mgl/Bureau/Travail/projets/alignement/alignement_global_unilingue/data/Source"
    #                             "/Sev_Z.xml")
    aligner.align(query=example_query_1, context=context_query_1, proportion=.20)
    # Le titre est plus variable et plus court, il est donc utile d'augmenter la fenêtre de comparaison à 1 voire 2 fois la taille de la division
    aligner.align(query=example_query_2, context=context_query_2, proportion=.5)
    for n in range(1, 17):
        # Il y a un problème qui fait que seule une boucle à ce niveau fonctionne
        print(n)
        context_query_3 = f"//tei:div[@type='chapitre'][@n = {n}]/descendant::tei:div"
        example_query_3 = "child::tei:p"
        aligner.align(query=example_query_3, context=context_query_3, proportion=0.5)
