module TableOfContents where

-- Trying to give a bird's eye view of the development

--------------------------------------------------------------------------------
-- Formulas

-- The expressions and formulas we deal with
import Representation

-- Their semantics
import Semantics

-- The subset of formulas we consider in various stages of the algorithm
import Properties

-- The notions of equivalence for formulas
import Equivalence

--------------------------------------------------------------------------------
-- Normalization

-- push negations inside
import Normalization.Negation
-- mergesort on the expressions seen as lists of variables
import Normalization.Linearisation
-- find the LCM of var0's  coefficients
import Normalization.LCMReduction
-- make all coefficients of var0 unitary
import Normalization.Unitarization

--------------------------------------------------------------------------------
-- Reduction to finite disjunctions

-- substitution & finite disjunction
import Disjunction
-- finite set of interesting values var0 can take
import Bset
-- equivalent formula if we let var0 tend to -∞
-- and bound under which it starts behaving that way
import Minusinf
-- Formulas which only have var0 in k∣e or k∤e are cyclic
-- (and thus equivalent to a finite disjunction)
import AllmostFree-prop
-- Formulas not satisfied by a finite disjunction hold at -∞ if they hold at all
import Cooper

--------------------------------------------------------------------------------
-- Quantifier elimination

-- for each intermediate representation
import Cooper.UnfCooper
import Cooper.LinCooper
import Cooper.NnfCooper

-- finally for QFree formulas and therefore all formulas
import Normalization.Qelimination

--------------------------------------------------------------------------------
-- Decision procedure
import Presburger
