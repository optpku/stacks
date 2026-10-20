module

public import ReasLib.Topology.Sheaf.ExtensionByInitial.Constant
public import ReasLib.Topology.Sheaf.Presentation
public import ReasLib.Topology.Sheaves.Types.Colimits
public import ReasLib.Topology.Sheaves.Types.Morphisms

/-!
# Presentations by lower-shriek constant sheaves

This module contains generator and presentation results for `Type`-valued sheaves built from the
lower-shriek constant functors on open subspaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open scoped TopCat

noncomputable section

universe u

namespace TopCat.Sheaf.ExtensionByInitial.Constant

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/-- A basis open together with a section of `F` on that open. -/
@[stacks 0CAH "basis sections"]
def BasisSection (B : Set (Opens X)) (F : TopCat.Sheaf (Type u) X) :=
  Σ U : B, F.presheaf.obj (Opposite.op (U : Opens X))

namespace BasisSection

/-- The basis open supporting a basis section. -/
def toOpen {B : Set (Opens X)} {F : TopCat.Sheaf (Type u) X}
    (i : BasisSection B F) : Opens X :=
  i.1

/-- The supporting open of a basis section belongs to the chosen basis. -/
theorem mem {B : Set (Opens X)} {F : TopCat.Sheaf (Type u) X}
    (i : BasisSection B F) : toOpen i ∈ B := sorry

/-- The section carried by a basis section. -/
def value {B : Set (Opens X)} {F : TopCat.Sheaf (Type u) X}
    (i : BasisSection B F) : F.presheaf.obj (Opposite.op (toOpen i)) :=
  i.2

/-- The canonical coproduct of one-point lower-shriek constant sheaves indexed by all basis
sections of `F`. -/
@[stacks 0CAH "canonical basis-section source"]
noncomputable def source (B : Set (Opens X)) (F : TopCat.Sheaf (Type u) X) :
    TopCat.Sheaf (Type u) X :=
  ∐ fun i : BasisSection B F ↦ j![toOpen i, PUnit]

/-- The map from the one-point lower-shriek summand indexed by `i` which classifies its carried
section of `F`. -/
@[stacks 0CAH "canonical basis-section component"]
noncomputable def component {B : Set (Opens X)} {F : TopCat.Sheaf (Type u) X}
    (i : BasisSection B F) : j![toOpen i, PUnit] ⟶ F :=
  (homEquivSection (toOpen i) PUnit F).symm (fun _ ↦ value i)

/-- The component indexed by a basis section classifies exactly that section. -/
@[stacks 0CAH "canonical basis-section component formula"]
theorem component_section {B : Set (Opens X)} {F : TopCat.Sheaf (Type u) X}
    (i : BasisSection B F) :
    homEquivSection (toOpen i) PUnit F (component i) = fun _ ↦ value i := sorry

/-- The canonical morphism from the coproduct indexed by all basis sections to `F`. -/
@[stacks 0CAH "canonical basis-section morphism"]
noncomputable def hom (B : Set (Opens X)) (F : TopCat.Sheaf (Type u) X) :
    source B F ⟶ F :=
  Limits.Sigma.desc fun i : BasisSection B F ↦ component i

/-- Restricting the canonical basis-section morphism to a coproduct summand gives the component
which classifies that section. -/
@[stacks 0CAH "canonical basis-section coproduct component"]
theorem ι_hom (B : Set (Opens X)) (F : TopCat.Sheaf (Type u) X)
    (i : BasisSection B F) :
    Limits.Sigma.ι (fun j : BasisSection B F ↦ j![toOpen j, PUnit]) i ≫ hom B F =
      component i := sorry

/-- If `B` is a basis, the canonical morphism indexed by all basis sections is epimorphic. -/
@[stacks 0CAH "canonical basis-section epimorphism"]
theorem hom_epi (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (F : TopCat.Sheaf (Type u) X) : Epi (hom B F) := sorry

end BasisSection

/-- Lemma 17.19.1: every `Type`-valued sheaf is an epimorphic image of a coproduct of
lower-shriek constant sheaves supported on basis opens, with finite indexing types. -/
@[stacks 0CAH]
theorem existsEpiFromBasis
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (F : TopCat.Sheaf (Type u) X) :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u)
      (hU : ∀ i, U i ∈ B) (hS : ∀ i, Finite (S i)),
      ∃ phi : (∐ fun i : I ↦ j![U i, S i]) ⟶ F, Epi phi := sorry

/-- Equation 17.19.2.1 (0CAJ): the canonical finite basis-presentation property is equivalent
to the source-facing description by a coequalizer of maps between finite coproducts of
lower-shriek constant sheaves with finite fibres. -/
@[stacks 0CAJ]
theorem basisPresentation_iff_exists
    (B : Set (Opens X)) (F : TopCat.Sheaf (Type u) X) :
    BasisPresentation.IsFinite B F ↔
      ∃ (m n : ℕ) (V : Fin m → Opens X) (U : Fin n → Opens X)
        (T : Fin m → Type u) (S : Fin n → Type u),
        (∀ j, V j ∈ B) ∧ (∀ i, U i ∈ B) ∧
          (∀ j, Finite (T j)) ∧ (∀ i, Finite (S i)) ∧
            ∃ (left right :
              (∐ fun j ↦ j![V j, T j]) ⟶ (∐ fun i ↦ j![U i, S i])),
              Nonempty (coequalizer left right ≅ F) := sorry

end TopCat.Sheaf.ExtensionByInitial.Constant

end

end
