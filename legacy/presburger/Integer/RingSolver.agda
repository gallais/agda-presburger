module Integer.RingSolver where

open import Integer.Structures

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module RingSolver =
 Solver (ACR.fromCommutativeRing ℤ+*-CommutativeRing)