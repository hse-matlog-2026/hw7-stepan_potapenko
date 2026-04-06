# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/some_proofs.py

"""Some proofs in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

# Some inference rules that only use conjunction.

#: Conjunction introduction inference rule
A_RULE = InferenceRule([Formula.parse('x'), Formula.parse('y')],
                       Formula.parse('(x&y)'))
#: Conjunction elimination (right) inference rule
AE1_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('y'))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('x'))

def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE1_RULE`, and
    `AE2_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE1_RULE`, and `AE2_RULE`.
    """
    # Task 4.7
    assumption = Formula.parse('(p&q)')
    conclusion = Formula.parse('(q&p)')
    statement = InferenceRule([assumption], conclusion)
    lines = [
        Proof.Line(assumption),
        Proof.Line(Formula.parse('q'), AE1_RULE, [0]),
        Proof.Line(Formula.parse('p'), AE2_RULE, [0]),
        Proof.Line(conclusion, A_RULE, [1, 2])
    ]
    return Proof(statement, {A_RULE, AE1_RULE, AE2_RULE}, lines)

def prove_I0() -> Proof:
    """Proves `~propositions.axiomatic_systems.I0` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I0` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 4.8
    conclusion = I0.conclusion
    statement = I0
    p_pp = Formula.parse('(p->(p->p))')
    p_pp_p = Formula.parse('(p->((p->p)->p))')
    d_part = Formula.parse('((p->((p->p)->p))->((p->(p->p))->(p->p)))')
    lines = [
        Proof.Line(p_pp_p, I1, []),
        Proof.Line(d_part, D, []),
        Proof.Line(Formula.parse('((p->(p->p))->(p->p))'), MP, [0, 1]),
        Proof.Line(p_pp, I1, []),
        Proof.Line(conclusion, MP, [3, 2])
    ]
    return Proof(statement, {MP, I1, D}, lines)

#: Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))

def prove_hypothetical_syllogism() -> Proof:
    """Proves `HS` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `HS` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 5.5
    statement = HS
    rules = {MP, I0, I1, D}
    p_q = Formula.parse('(p->q)')
    q_r = Formula.parse('(q->r)')
    p_r = Formula.parse('(p->r)')
    i1_spec = Formula.parse('((q->r)->(p->(q->r)))')
    p_qr = Formula.parse('(p->(q->r))')
    d_spec = Formula.parse('((p->(q->r))->((p->q)->(p->r)))')
    pq_pr = Formula.parse('((p->q)->(p->r))')
    lines = [
        Proof.Line(p_q),
        Proof.Line(q_r),
        Proof.Line(i1_spec, I1, []),
        Proof.Line(p_qr, MP, [1, 2]),
        Proof.Line(d_spec, D, []),
        Proof.Line(pq_pr, MP, [3, 4]),
        Proof.Line(p_r, MP, [0, 5])
    ]

    return Proof(statement, rules, lines)

def prove_I2() -> Proof:
    """Proves `~propositions.axiomatic_systems.I2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7a
    p = Formula.parse('p')
    np = Formula.parse('~p')
    nq = Formula.parse('~q')
    # Доказываем ~p из допущений {~p, p, ~q}
    # prove_by_way_of_contradiction возьмет это и докажет q
    inner = Proof(InferenceRule([np, p, nq], np), {MP}, [Proof.Line(np)])

    # Здесь критический момент: эти функции ОБЯЗАНЫ возвращать Proof
    step1 = prove_by_way_of_contradiction(inner)  # |- q (из ~p, p)
    step2 = remove_assumption(step1)  # |- p -> q (из ~p)
    return remove_assumption(step2)

#: Double-negation elimination
_NNE = InferenceRule([], Formula.parse('(~~p->p)'))

def _prove_NNE() -> Proof:
    """Proves `_NNE` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_NNE` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7b
    nnp = Formula.parse('~~p')
    np = Formula.parse('~p')
    # Допущения: ~~p, ~np (т.е. ~~~p). Но нам нужно p.
    # {~~p, ~p} |- ~~p и {~~p, ~p} |- ~p.
    inner = Proof(InferenceRule([nnp, np], nnp), {MP}, [Proof.Line(nnp)])
    return prove_by_way_of_contradiction(inner)

def prove_NN() -> Proof:
    """Proves `~propositions.axiomatic_systems.NN` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NN` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7c
    p = Formula.parse('p')
    np = Formula.parse('~p')
    # {p, ~p} |- p
    inner = Proof(InferenceRule([p, np], p), {MP}, [Proof.Line(p)])
    return remove_assumption(prove_by_way_of_contradiction(inner))

#: Contraposition
_CP = InferenceRule([], Formula.parse('((p->q)->(~q->~p))'))

def _prove_CP() -> Proof:
    """Proves `_CP` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CP` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7d
    pq = Formula.parse('(p->q)')
    nq = Formula.parse('~q')
    p = Formula.parse('p')
    # {p->q, ~q, p} |- q и ~q => contradiction
    inner = Proof(
        InferenceRule([pq, nq, p], Formula.parse('~(p->p)')),
        {MP, NI},
        [Proof.Line(p),
         Proof.Line(pq),
         Proof.Line(Formula.parse('q'), MP, [0, 1]),
         Proof.Line(nq),
         Proof.Line(Formula('->', Formula.parse('q'), Formula('->', nq, Formula.parse('~(p->p)'))), NI, []),
         Proof.Line(Formula('->', nq, Formula.parse('~(p->p)')), MP, [2, 4]),
         Proof.Line(Formula.parse('~(p->p)'), MP, [3, 5])]
    )
    return remove_assumption(remove_assumption(prove_by_way_of_contradiction(inner)))

def prove_NI() -> Proof:
    """Proves `~propositions.axiomatic_systems.NI` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NI` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7e
    p = Formula.parse('p')
    np = Formula.parse('~p')
    inner = Proof(
        InferenceRule([p, np], Formula.parse('~(p->p)')),
        {MP, NI},
        [Proof.Line(p),
         Proof.Line(np),
         Proof.Line(Formula('->', p, Formula('->', np, Formula.parse('~(p->p)'))), NI, []),
         Proof.Line(Formula('->', np, Formula.parse('~(p->p)')), MP, [0, 2]),
         Proof.Line(Formula.parse('~(p->p)'), MP, [1, 3])]
    )
    return remove_assumption(remove_assumption(inner))

#: Consequentia mirabilis
_CM = InferenceRule([Formula.parse('(~p->p)')], Formula.parse('p'))

def _prove_CM() -> Proof:
    """Proves `_CM` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CM` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7f
    npp = Formula.parse('(~p->p)')
    np = Formula.parse('~p')
    # {~p->p, ~p} |- p и ~p => contradiction
    inner = Proof(
        InferenceRule([npp, np], Formula.parse('~(p->p)')),
        {MP, NI},
        [Proof.Line(np),
         Proof.Line(npp),
         Proof.Line(Formula.parse('p'), MP, [0, 1]),
         Proof.Line(np),
         Proof.Line(Formula('->', Formula.parse('p'), Formula('->', np, Formula.parse('~(p->p)'))), NI, []),
         Proof.Line(Formula('->', np, Formula.parse('~(p->p)')), MP, [2, 4]),
         Proof.Line(Formula.parse('~(p->p)'), MP, [3, 5])]
    )
    return prove_by_way_of_contradiction(inner)

def prove_R() -> Proof:
    """Proves `~propositions.axiomatic_systems.R` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.R` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7g
    pq = Formula.parse('(p->q)')
    npq = Formula.parse('(~p->q)')
    nq = Formula.parse('~q')
    # {pq, npq, nq} |- p->q, ~q => ~p  И  ~p->q, ~q => p. Противоречие.
    # Используем N (contraposition)
    inner = Proof(
        InferenceRule([pq, npq, nq], Formula.parse('~(p->p)')),
        {MP, NI, N, I1, D, I0},
        [Proof.Line(nq),
         Proof.Line(pq),
         Proof.Line(Formula('->', pq, Formula('->', nq, Formula.parse('~p'))), _prove_CP().statement,
                    _prove_CP().lines),
         Proof.Line(Formula('->', nq, Formula.parse('~p')), MP, [1, 2]),
         Proof.Line(Formula.parse('~p'), MP, [0, 3]),
         Proof.Line(npq),
         # Аналогично для ~~p
         Proof.Line(Formula('->', npq, Formula('->', nq, Formula.parse('~~p'))), N, []),
         Proof.Line(Formula('->', nq, Formula.parse('~~p')), MP, [5, 6]),
         Proof.Line(Formula.parse('~~p'), MP, [0, 7]),
         Proof.Line(Formula('->', Formula.parse('~~p'), Formula('->', Formula.parse('~p'), Formula.parse('~(p->p)'))),
                    NI, []),
         Proof.Line(Formula('->', Formula.parse('~p'), Formula.parse('~(p->p)')), MP, [8, 9]),
         Proof.Line(Formula.parse('~(p->p)'), MP, [4, 10])]
    )
    return remove_assumption(remove_assumption(prove_by_way_of_contradiction(inner)))

def prove_N() -> Proof:
    """Proves `~propositions.axiomatic_systems.N` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N_ALTERNATIVE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.N` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N_ALTERNATIVE`.
    """
    # Optional Task 6.8
    pq = Formula.parse('(p->q)')
    nq = Formula.parse('~q')
    p = Formula.parse('p')
    # {p->q, ~q, p} |- contradiction
    inner = Proof(
        InferenceRule([pq, nq, p], Formula.parse('~(p->p)')),
        {MP, NI},
        [Proof.Line(p), Proof.Line(pq), Proof.Line(Formula.parse('q'), MP, [0, 1]),
         Proof.Line(nq),
         Proof.Line(Formula('->', Formula.parse('q'), Formula('->', nq, Formula.parse('~(p->p)'))), NI, []),
         Proof.Line(Formula('->', nq, Formula.parse('~(p->p)')), MP, [2, 4]),
         Proof.Line(Formula.parse('~(p->p)'), MP, [3, 5])]
    )
    # Используем правила, доступные в 6.8 (включая N_ALTERNATIVE)
    # prove_by_way_of_contradiction вернет доказательство, использующее N.
    # Если N в системе заменено на N_ALTERNATIVE, функции дедукции сработают корректно.
    return remove_assumption(remove_assumption(prove_by_way_of_contradiction(inner)))

def prove_NA1() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA1` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE1`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA1` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE1`.
    """
    # Optional Task 6.9a

def prove_NA2() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE2`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE2`.
    """
    # Optional Task 6.9b

def prove_NO() -> Proof:
    """Proves `~propositions.axiomatic_systems.NO` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.OE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NO` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.OE`.
    """
    # Optional Task 6.9c
