import copy
import glob
import json
import os
import random
import string
import traceback
import datetime
import collatex
import lxml.etree as ET



def generateur_id(size=6, chars=string.ascii_uppercase + string.ascii_lowercase + string.digits) -> str:
    random_string = ''.join(random.choice(chars) for _ in range(size))
    return random_string


def log_stamp():
    if os.path.isdir("logs"):
        pass
    else:
        os.makedirs("logs")
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
    # On produit l'alignement un à un
    aligned_table = list(zip([token[0] if token else None for token in json_table['table'][0]],
                             [token[0] if token else None for token in json_table['table'][1]]))

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
    def __init__(self, target_path: str, source_file: str, output_files_prefix: str):
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
        self.output_file_prefix = output_files_prefix

        # On crée les arbres de sortie à partir des arbres d'entrée
        self.output_tree = {key: copy.deepcopy(tree) for key, tree in self.dict_of_parsed_files.items()}

        self.target_tokens, self.target_ids, self.tokens_and_ids = dict(), dict(), dict()

    def structure_tree(self, elements: list, ids: list, context, index_context, target_id):
        elements_and_ids = list(zip(elements, ids))
        context_target_nodes = self.output_tree[target_id].xpath(context, namespaces=self.ns_decl)[index_context]
        all_nodes = context_target_nodes.xpath(f"descendant::node()[not(self::text())]", namespaces=self.ns_decl)
        all_ids = context_target_nodes.xpath(
            f"descendant::node()[not(self::text())]/@*[name()='n' or name()='xml:id']", namespaces=self.ns_decl)
        nodes_and_ids = list(zip(all_nodes, all_ids))

        # Chaque itération correspond à une structure à insérer dans le document cible
        for index, (element, (min_id, max_id)) in enumerate(elements_and_ids):
            element_name = element.xpath("name()")
            # On récupère les attributs sous la forme d'un dictionnaire
            attributes = element.attrib
            print(element_name)

            # Va savoir pourquoi mais l'argument nsmap ne fonctionne pas ici il faut passer par ce truc moche.
            element_to_insert = ET.Element("{" + self.tei_ns + "}" + element_name)
            for attribute, value in attributes.items():
                element_to_insert.set(attribute, value.replace(self.source_file_id, target_id))

            # On fonctionne différemment pour le premier élément de la liste: dans ce cas il faut chercher
            # le premier token de la structure. Si tel n'est pas le cas, on va chercher le 2e token (car on prévoit
            # d'insérer l'élément juste après le premier qui correspond au dernier élément de la structure antérieure)
            if index != 0:
                following_anchor = \
                    [nodes_and_ids[index + 1][0] for index, (node, ident) in enumerate(nodes_and_ids) if
                     ident == min_id][0]
            else:
                following_anchor = [node for index, (node, ident) in enumerate(nodes_and_ids) if ident == min_id][0]
            following_anchor.addprevious(element_to_insert)
            print(f"Placing anchor before element {following_anchor.xpath('@xml:id')}")

            #  On cherche ici les positions (dans le contexte donné) des ancres de début et de fin de division
            # On convertit donc un identifiant en index.
            # On doit toujours mettre à jour notre arbre en parsant à chaque nouvelle boucle
            context_target_nodes = self.output_tree[target_id].xpath(context, namespaces=self.ns_decl)[index_context]
            all_nodes = context_target_nodes.xpath(f"child::node()[not(self::text())]", namespaces=self.ns_decl)
            for idx, node in enumerate(all_nodes):
                # On commence par chercher le premier mot de la structure
                if index == 0:
                    # Tous les noeuds ne sont pas forcément identifiés par un xml:id
                    if len(node.xpath("@xml:id")) > 0:
                        if node.xpath("@xml:id")[0] == min_id:
                            min_position_in_full_list = idx
                            print(f"Minimal pos found for first loop: {min_position_in_full_list}")
                    else:
                        pass
                else:
                    if len(node.xpath("@xml:id")) > 0:
                        if node.xpath("@xml:id")[0] == following_anchor.xpath("@xml:id")[0]:
                            print("Minimal pos found")
                            min_position_in_full_list = idx
                    else:
                        pass

                # Maintenant on cherche le dernier mot de la structure
                if len(node.xpath("@xml:id")) > 0:
                    if node.xpath("@xml:id")[0] == max_id:
                        print("Maximal pos found")
                        max_position_in_full_list = idx
            print(f"Minimal range id: {min_id} | Maximal range id: {max_id}")
            print(f"Positions: {min_position_in_full_list} and {max_position_in_full_list}")

            # On sélectionne les noeuds à insérer en faisant attention à l'index
            if index == 0:
                items_to_shift = all_nodes[min_position_in_full_list: max_position_in_full_list + 1]
            else:
                items_to_shift = all_nodes[min_position_in_full_list: max_position_in_full_list + 1]

            # Finalement, on insère les noeuds dans la division nouvellement créee
            for word in items_to_shift:
                try:
                    element_to_insert.append(word)
                except ValueError:
                    print(traceback.format_exc())
                    print(word)

        # La division est créée, les noeuds insérés. Travail accompli.
        print("Done !")

    def align(self, query, context, text_proportion):
        # On réalise la même opération avec le texte source et un texte cible qui change à chaque fois.
        for target_document in self.output_tree.keys():
            print(f"Trying to align {target_document} on {query} with {context} context.")
            # On va itérer sur chaque division
            # On prend le nombre de mots de la division source,
            # et on va chercher dans cette zone à aligner la source et la cible
            # Pour la première division c'est facile
            # Pour la suite, il faut mettre à jour la zone en fonction de la longueur de la division de la cible
            # Point faible de cette méthode: ça fonctionne de manière incrémentielle,
            # et si ça bloque quelque part, le processus complet est bloqué.
            # Il faudra probablement recourir à une méthode de text reuse en complément.
            context_source_nodes = self.source_file.xpath(context, namespaces=self.ns_decl)
            context_target_nodes = self.output_tree[target_document].xpath(context, namespaces=self.ns_decl)
            for index_context, (context_source_node, context_target_node) in enumerate(
                    list(zip(context_source_nodes, context_target_nodes))):
                structure_source_elements = context_source_node.xpath(query, namespaces=self.ns_decl)
                structure_target_elements = context_target_node.xpath(query, namespaces=self.ns_decl)

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
                assert len(target_lemmas) == len(target_tokens), "Merci de vérifier que le corpus-cible est lemmatisé"

                target_ids = context_target_node.xpath("descendant::node()[self::tei:w or self::tei:pc]/@xml:id",
                                                       namespaces=self.ns_decl)
                target_tokens_ids = list(zip(target_tokens, target_ids))
                current_source_position = 0
                current_target_position = 0
                source_lemmas = context_source_node.xpath("descendant::node()[self::tei:w or self::tei:pc]/@lemma",
                                                          namespaces=self.ns_decl)
                source_ids = context_source_node.xpath("descendant::node()[self::tei:w or self::tei:pc]/@xml:id",
                                                       namespaces=self.ns_decl)
                assert len(source_ids) == len(source_lemmas), "Merci de vérifier que le corpus-source est lemmatisé"

                source_lemmas_ids = list(zip(source_lemmas, source_ids))
                target_id_list = [target_ids[0], ]
                # On itère sur chaque division
                matching_id = str
                for index, division in enumerate(structure_source_elements):

                    # On a besoin de l'identifiant de fin de la division courante du
                    # document source. On va
                    # ensuite regarder si ce token est dans la table alignée, pour identifier
                    # la fin de la division du document cible.
                    # TODO: ici ajouter la possibilité de travailler sur un document en partie structuré
                    # (exemple: un test dans le document cible pour voir si la division existe.) Si elle existe, on
                    # passe à la division suivante en prenant le dernier xml:id comme ancre.
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

                    # Ici on permet au programme d'ajuster la position en fonction des divisions trouvées antérieurement.
                    current_source_position += number_of_tokens_in_div
                    # Pour la première division du contexte, pas besoin d'incrémenter à la position antérieure
                    if index == 0:
                        current_target_position = number_of_tokens_in_div
                    else:
                        # On va aller chercher à partir de la dernière position trouvée.
                        current_target_position = number_of_tokens_in_div + [index for index, (token, ident) in enumerate(target_tokens_ids) if ident == matching_id][0]
                    # On va aller collationner le texte dans une fenêtre où l'on estime que la division termine
                    # En fonction de la variabilité de la division en question on choisira une text_proportion différente
                    tokens_fraction = round(number_of_tokens_in_div * text_proportion)
                    source_search_range = [max(0, current_source_position - tokens_fraction),
                                           current_source_position + tokens_fraction]

                    target_search_range = [max(0, current_target_position - tokens_fraction),
                                           current_target_position + tokens_fraction]
                    print(f"Division {index + 1}")
                    print(f"Last matching id: {matching_id}")
                    print(f"Current target position: {current_target_position}")
                    print(f"Source search range: {source_search_range}")
                    print(f"Target search range: {target_search_range}")
                    source_tokens_to_compare = source_lemmas_ids[source_search_range[0]: source_search_range[1]]

                    # On crée les données tel que le veut collatex
                    source_list = [{"t": lemma, "xml:id": id} for lemma, id in source_tokens_to_compare]
                    collatex_dict = {"witnesses": [{"id": f"{self.source_file_id}", "tokens": source_list}]}
                    zip_target_token_id = list(zip(target_lemmas, target_ids))

                    # Si on est dans la première division du contexte, on prend les infos de la source comme fenêtre
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
                    except KeyError:
                        print(f"Error with query {query} and context {context}")
                        print(traceback.format_exc())
                    try:
                        # Ici on va regarder si le résultat de la collation correspond à un alignement effectif.
                        # Le cas échéant, on récupère l'identifiant du token qui fait borne.
                        match, matching_id = check_if_match(json_table=collation_table,
                                                            target_id=last_token_current_div)
                        print(f"Div {index + 1} aligned.")
                        # On nourrit ici une liste de couples d'identifiants qui va correspondre à la position
                        # des divisions à créer.
                        target_id_list.append(matching_id)
                    except Exception:
                        # L'erreur d'alignement mène logiquement à la fin du travail sur le contexte en cours
                        # (on passe au chapitre suivant en cas de travail sur les paragraphes par exemple)
                        # TODO: il faut pouvoir travailler à partir d'un arbre déjà en partie structuré
                        print(traceback.format_exc())
                        print(last_token_current_div)
                        print(f"Unable to align div {index + 1}. Please check structure in source document.")
                        write_log(
                            f"Alignment error for target file {target_document}.")
                        try:
                            unparsed_divs = structure_source_elements[index:len(structure_source_elements)]
                            unparsed_ids = [division.xpath("@n")[0] if len(division.xpath("@n")) > 0 else division.xpath("@xml:id")[0] for division in unparsed_divs]
                            message = f"Divisions {', '.join(unparsed_ids)} will not appear in the final document leaving the tokens unstructured."
                            write_log(message)
                        except Exception:
                            print(traceback.format_exc())
                        break

                target_id_list = [(target_id_list[index], target_id_list[index + 1]) for index, _
                                  in enumerate(target_id_list[:len(target_id_list) - 1])]
                # On a donc notre liste de tuples, on va pouvoir créer l'arbre à l'aide de structure_tree.
                print("Structuring tree:")
                try:
                    self.structure_tree(elements=structure_source_elements,
                                        ids=target_id_list, context=context,
                                        index_context=index_context, target_id=target_document)
                except Exception:
                    traceback.print_exc()
                    exit(0)
            
            try:
                os.makedirs("data/results/")
            except FileExistsError:
                pass
            # On écrit l'arbre dans le fichier xml correspondant.
            write_tree(f"data/results/{target_document}{self.output_file_prefix}.xml",
                        self.output_tree[target_document])


