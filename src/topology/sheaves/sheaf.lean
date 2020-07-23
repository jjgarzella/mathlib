
import .presheaf

universes u v

open category_theory
open topological_space

variables {C : Type u} [𝒞 : category.{v} C]
variables {X : Top.{v}}
include 𝒞

#check @Top.presheaf

def is_sheaf (pre : X.presheaf C) : Prop :=
sorry
-- identity axiom
-- gluability axiom
--       OR
-- preserves (or reflects?) limits in the
--   shape of a covering diagram
