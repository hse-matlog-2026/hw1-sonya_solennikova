# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2025
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))

    if is_variable(formula.root):
        return model[formula.root]
    
    if is_constant(formula.root):
        return True if formula.root == 'T' else False
    
    if is_unary(formula.root):
        return not evaluate(formula.first, model)
    
    left_val = evaluate(formula.first, model)
    right_val = evaluate(formula.second, model)
    
    if formula.root == '&':
        return left_val and right_val
    elif formula.root == '|':
        return left_val or right_val
    elif formula.root == '->':
        return (not left_val) or right_val
    else:  
        return left_val != right_val

    # Task 2.1

def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Parameters:
        variables: variable names over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variable names. The
        order of the models is lexicographic according to the order of the given
        variable names, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)

    n = len(variables)
    for i in range(2**n):
        model = {}
        for j, var in enumerate(variables):
            bit = (i >> (n - j - 1)) & 1
            model[var] = bool(bit)
        yield model
    # Task 2.2

def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
     for m in models:
        yield evaluate(formula, m)
    # Task 2.3

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    vars_list = sorted(formula.variables())
    

    header = " | ".join(vars_list + [str(formula)])
    print(f"| {header} |")
    

    sep = " | ".join(["-" * len(v) for v in vars_list] + ["-" * len(str(formula))])
    print(f"|{sep}|")
    

    for m in all_models(vars_list):
        row_vals = []
        for v in vars_list:
            val = m[v]
            row_vals.append("T" if val else "F")
        
        result = evaluate(formula, m)
        row_vals.append("T" if result else "F")
        
        row = " | ".join(row_vals)
        print(f"| {row} |")
    # Task 2.4

def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    vars_list = list(formula.variables())
    for m in all_models(vars_list):
        if not evaluate(formula, m):
            return False
    return True
    # Task 2.5a

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    vars_list = list(formula.variables())
    for m in all_models(vars_list):
        if evaluate(formula, m):
            return False
    return True
    # Task 2.5b

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
     vars_list = list(formula.variables())
    for m in all_models(vars_list):
        if evaluate(formula, m):
            return True
    return False
    # Task 2.5c

def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    vars_list = list(model.keys())
    result = None
    
    for v in vars_list:
        if model[v]:
            literal = Formula(v)
        else:
            literal = Formula('~', Formula(v))
        
        if result is None:
            result = literal
        else:
            result = Formula('&', result, literal)
    
    return result
    # Task 2.6

def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\\ ``(``\\ `~synthesize.variables`\\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    clauses = []
    vals_list = list(values)
    
    for i, m in enumerate(all_models(variables)):
        if vals_list[i]: 
            clause = _synthesize_for_model(m)
            clauses.append(clause)
    
    if not clauses:
        return Formula('&', Formula('p'), Formula('~', Formula('p')))
    
    result = clauses[0]
    for c in clauses[1:]:
        result = Formula('|', result, c)
    
    return result
    # Task 2.7

def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    vs = list(model.keys())
    r = None
    
    for v in vs:
        if not model[v]:
            l = Formula(v)
        else:
            l = Formula('~', Formula(v))
        
        if r is None:
            r = l
        else:
            r = Formula('|', r, l)
    
    return r
    # Optional Task 2.8

def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\\ ``(``\\ `~synthesize.variables`\\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    fs = []
    vs = list(values)
    
    for i, m in enumerate(all_models(variables)):
        if not vs[i]:
            f = _synthesize_for_all_except_model(m)
            fs.append(f)
    
    if not fs:
        return Formula('|', Formula('p'), Formula('~', Formula('p')))
    
    r = fs[0]
    for f in fs[1:]:
        r = Formula('&', r, f)
    
    return r
    # Optional Task 2.9

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
