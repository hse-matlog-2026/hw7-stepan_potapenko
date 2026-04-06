# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2025
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\\ `antecedent`\\ ``->``\\ `consequent`\\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\\ `antecedent`\\ ``->``\\ `consequent`\\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    antecedent = antecedent_proof.statement.conclusion
    new_lines = list(antecedent_proof.lines)
    new_lines.append(Proof.Line(Formula('->', antecedent, consequent), conditional, []))
    new_lines.append(Proof.Line(consequent, MP, [len(new_lines) - 2, len(new_lines) - 1]))
    return Proof(InferenceRule(antecedent_proof.statement.assumptions, consequent),
                 antecedent_proof.rules | {MP, conditional}, new_lines)

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\\ `antecedent1`\\ ``->(``\\ `antecedent2`\\ ``->``\\ `consequent`\\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\\ `antecedent1`\\ ``->(``\\ `antecedent2`\\ ``->``\\ `consequent`\\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b
    a1 = antecedent1_proof.statement.conclusion
    a2 = antecedent2_proof.statement.conclusion
    new_lines = list(antecedent1_proof.lines)
    shift = len(new_lines)
    for line in antecedent2_proof.lines:
        if line.is_assumption():
            new_lines.append(line)
        else:
            new_assumptions = tuple(a + shift for a in line.assumptions)
            new_lines.append(Proof.Line(line.formula, line.rule, new_assumptions))
    idx_a1 = shift - 1
    idx_a2 = len(new_lines) - 1
    axiom_formula = Formula('->', a1, Formula('->', a2, consequent))
    new_lines.append(Proof.Line(axiom_formula, double_conditional, []))
    idx_axiom = len(new_lines) - 1
    new_lines.append(Proof.Line(Formula('->', a2, consequent), MP, [idx_a1, idx_axiom]))
    idx_intermediate = len(new_lines) - 1
    new_lines.append(Proof.Line(consequent, MP, [idx_a2, idx_intermediate]))
    return Proof(InferenceRule(antecedent1_proof.statement.assumptions, consequent),
                 antecedent1_proof.rules | {MP, double_conditional}, new_lines)

def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\\ `assumption`\\ ``->``\\ `conclusion`\\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\\ `assumption`\\ ``->``\\ `conclusion`\\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    gamma = proof.statement.assumptions[:-1]
    psi = proof.statement.assumptions[-1]
    new_lines = []

    for i, line in enumerate(proof.lines):
        phi_i = line.formula
        if phi_i == psi and line.is_assumption():
            new_lines.append(Proof.Line(Formula('->', psi, psi), I0, []))
        elif line.is_assumption() or (line.rule and len(line.rule.assumptions) == 0):
            if line.is_assumption():
                new_lines.append(Proof.Line(phi_i))
            else:
                new_lines.append(Proof.Line(phi_i, line.rule, []))
            new_lines.append(Proof.Line(Formula('->', phi_i, Formula('->', psi, phi_i)), I1, []))
            new_lines.append(Proof.Line(Formula('->', psi, phi_i), MP, [len(new_lines) - 2, len(new_lines) - 1]))
        else:
            pass
    mapping = {}
    new_lines = []
    for i, line in enumerate(proof.lines):
        phi_i = line.formula
        if phi_i == psi and line.is_assumption():
            new_lines.append(Proof.Line(Formula('->', psi, psi), I0, []))
        elif line.is_assumption() or (line.rule and len(line.rule.assumptions) == 0):
            new_lines.append(line)
            new_lines.append(Proof.Line(Formula('->', phi_i, Formula('->', psi, phi_i)), I1, []))
            new_lines.append(Proof.Line(Formula('->', psi, phi_i), MP, [len(new_lines) - 2, len(new_lines) - 1]))
        else:
            j, k = line.assumptions
            phi_j = proof.lines[j].formula
            new_lines.append(Proof.Line(Formula('->', Formula('->', psi, Formula('->', phi_j, phi_i)),
                                                Formula('->', Formula('->', psi, phi_j), Formula('->', psi, phi_i))), D,
                                        []))
            new_lines.append(Proof.Line(Formula('->', Formula('->', psi, phi_j), Formula('->', psi, phi_i)), MP,
                                        [mapping[k], len(new_lines) - 1]))
            new_lines.append(Proof.Line(Formula('->', psi, phi_i), MP, [mapping[j], len(new_lines) - 1]))
        mapping[i] = len(new_lines) - 1
    return Proof(InferenceRule(gamma, Formula('->', psi, proof.statement.conclusion)),
                 proof.rules | {MP, I0, I1, D}, new_lines)

def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\\ `affirmation`\\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\\ `affirmation`\\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)

def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\\ `formula`\\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\\ `formula`\\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\\ `formula`\\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    proof_with_removed = remove_assumption(proof)
    phi = proof.statement.assumptions[-1].first
    new_lines = list(proof_with_removed.lines)
    idx_removed_phi = len(new_lines) - 1
    f_p_p = Formula.parse('(p->p)')
    n_specialization = Formula('->', Formula('->', Formula('~', phi), Formula('~', f_p_p)),
                               Formula('->', f_p_p, phi))
    new_lines.append(Proof.Line(n_specialization, N, []))
    idx_n_axiom = len(new_lines) - 1
    new_lines.append(Proof.Line(Formula('->', f_p_p, phi), MP, [idx_removed_phi, idx_n_axiom]))
    idx_cond_phi = len(new_lines) - 1
    new_lines.append(Proof.Line(f_p_p, I0, []))
    idx_p_p = len(new_lines) - 1
    new_lines.append(Proof.Line(phi, MP, [idx_p_p, idx_cond_phi]))
    return Proof(InferenceRule(proof_with_removed.statement.assumptions, phi),
                 proof_with_removed.rules | {MP, I0, I1, D, N}, new_lines)