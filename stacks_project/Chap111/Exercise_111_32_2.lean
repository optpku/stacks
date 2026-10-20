module

public import ReasLib.Topology.Sheaves.Types.Morphisms
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopCat.Presheaf

universe u

variable {X : TopCat.{u}} {ℱ 𝒢 : X.Sheaf (Type u)} (φ : ℱ ⟶ 𝒢)

/- Exercise 111.32.2: a morphism of sheaves of sets on `X` is an isomorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is bijective. -/
@[stacks 078Y] #check (TopCat.Sheaf.isIso_iff_stalk_bijective φ :
  IsIso φ ↔ ∀ x : X, Function.Bijective ((stalkFunctor (Type u) x).map φ.hom))
