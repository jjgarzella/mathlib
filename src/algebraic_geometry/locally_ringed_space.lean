-- locally ringed spaces

import tactic

import topology.basic
import algebraic_geometry.presheafed_space
import algebra.category.CommRing
import topology.sheaves.sheaf
import .stalks
import ring_theory.ideals

open algebraic_geometry
-- open algebraic_geometry.PresheafedSpace
structure ringed_space :=
(X : PresheafedSpace CommRing)
(sheafy : is_sheaf X.𝒪)

structure locally_ringed_space extends ringed_space :=
(locality : ∀ x : X,
  local_ring (@PresheafedSpace.stalk CommRing _ _ to_ringed_space.X x))
