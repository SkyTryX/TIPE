from random import randint, getrandbits
from math import floor


def SAT_formule_gen(l):
    string = "("
    for i in range(l):
        b = bool(getrandbits(1))
        if i % 2 == 0:
            string += f"And("
        else:
            string += f"Or("
        if b:
            string += f"Var {randint(0, 10)},"
        else:
            string += f"Not(Var {randint(0, 10)}),"
    if b:
        string += f"Var {randint(0, 10)}"
    else:
        string += f"Not(Var {randint(0, 10)})"
    string += (l+1)*")"
    return string

def alternee_formule_gen(l, nb_lit):
    string = "("
    for i in range(l):
        b = bool(getrandbits(1))
        if i % 2 == 0:
            string += f"And("
        else:
            string += f"Or("
        if b:
            string += f"(\"{randint(0, nb_lit)}\", true),"
        else:
            string += f"(\"{randint(0, nb_lit)}\", false),"
    if b:
        string += f"Atom(\"{randint(0, nb_lit)}\", true)"
    else:
        string += f"Atom(\"{randint(0, nb_lit)}\", false)"
    string += (l+1)*")"
    return string

def both_gen(l, nb_lit):
    alt_str = "("
    sat_str = "("
    dpl_str = ""
    for i in range(l):
        b = bool(getrandbits(1))
        if i % 2 == 0:
            alt_str += f"And("
            sat_str += f"And("
        else:
            alt_str += f"Or("
            sat_str += f"Or("
        number = randint(0, nb_lit)
        
        if b:
            alt_str += f"(\"{number}\", true),"
            sat_str += f"Var {number},"
            dpl_str += f"{number}"
        else:
            alt_str += f"(\"{number}\", false),"
            sat_str += f"Not(Var {number}),"
            dpl_str += f"-{number}"
        
        if i % 2 == 0:
            dpl_str += " & ("
        else:
            dpl_str += " | ("
    number = randint(0, nb_lit)
    if b:
        alt_str += f"Atom(\"{number}\", true)"
        sat_str += f"Var {number}"
        dpl_str += f"{number}"
    else:
        alt_str += f"Atom(\"{number}\", false)"
        sat_str += f"Not(Var {number})"
        dpl_str += f"-{number}"
    alt_str += (l+1)*")"
    sat_str += (l+1)*")"
    dpl_str += l*")"
    return alt_str, sat_str, dpl_str

txt_alt = "[|"
txt_sat = "[|"
txt_dpl = ""
for i in range(1, 101):
    res = both_gen(i, randint(0, floor(i/2)))
    txt_alt += res[0]+";\n"
    txt_sat += res[1]+";\n"
    txt_dpl += res[2]+"\n"
txt_alt += "|]"
txt_sat += "|]"
with open("tests_alt.txt", "w") as f_alt:
    f_alt.write(txt_alt)
with open("tests_quine.txt", "w") as f_sat:
    f_sat.write(txt_sat)
with open("tests_dpll.txt", "w") as f_dpll:
    f_dpll.write(txt_dpl)