/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Functor
public import ReasLib.CategoryTheory.Limits.Retract

/-!
# Colimits of Binary Biproducts of Diagrams

This file constructs the colimit of a pointwise binary biproduct from colimits of its two
summands.  It also records the comparison isomorphism and its component formulas.  Together with
retract stability of `HasColimit`, this gives the existence criterion for binary biproducts of
diagrams in an idempotent-complete target category.
-/

@[expose] public section

open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

universe uJ vJ uC vC

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
variable (F G : J ⥤ C)

section Colimits

variable [HasColimit F] [HasColimit G]

namespace PointwiseBiprodColimit

/-- The component of the canonical cocone from the explicit pointwise binary biproduct diagram
to `colimit F ⊞ colimit G`. -/
noncomputable def ι (j : J) :
    (pointwiseBinaryBicone F G).pt.obj j ⟶ colimit F ⊞ colimit G :=
  biprod.map (colimit.ι F j) (colimit.ι G j)

/-- The pointwise biproduct colimit legs are natural in the diagram index. -/
theorem ι_naturality {i j : J} (f : i ⟶ j) :
    (pointwiseBinaryBicone F G).pt.map f ≫ ι F G j =
      ι F G i ≫
        ((Functor.const J).obj (colimit F ⊞ colimit G)).map f := sorry

/-- The descent morphism from the binary biproduct of the two colimits to a competing cocone. -/
noncomputable def desc (s : Cocone (pointwiseBinaryBicone F G).pt) :
    colimit F ⊞ colimit G ⟶ s.pt :=
  biprod.desc
    (colimit.desc F ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s))
    (colimit.desc G ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s))

/-- The canonical descent morphism commutes with each cocone leg. -/
theorem desc_fac (s : Cocone (pointwiseBinaryBicone F G).pt) (j : J) :
    ι F G j ≫ desc F G s = s.ι.app j := sorry

/-- The canonical descent morphism is uniquely determined by its composites with the cocone
legs. -/
theorem desc_uniq (s : Cocone (pointwiseBinaryBicone F G).pt)
    (m : colimit F ⊞ colimit G ⟶ s.pt)
    (hm : ∀ j : J, ι F G j ≫ m = s.ι.app j) :
    m = desc F G s := sorry

/-- The selected colimit cocone of the explicit pointwise binary biproduct diagram.  Its vertex,
legs, and descent operation are concrete; only their laws are deferred. -/
noncomputable def colimitCocone :
    ColimitCocone (pointwiseBinaryBicone F G).pt where
  cocone :=
    { pt := colimit F ⊞ colimit G
      ι :=
        { app := ι F G
          naturality := fun _ _ f ↦ ι_naturality F G f } }
  isColimit :=
    { desc := desc F G
      fac := desc_fac F G
      uniq := desc_uniq F G }

end PointwiseBiprodColimit

/-- If two diagrams admit colimits, then their explicit pointwise binary biproduct admits a
colimit. -/
noncomputable instance hasColimit_pointwiseBiprod :
    HasColimit (pointwiseBinaryBicone F G).pt :=
  HasColimit.mk (PointwiseBiprodColimit.colimitCocone F G)

/-- If two diagrams admit colimits, then their chosen binary biproduct in the functor category
admits a colimit. -/
noncomputable instance hasColimit_biprod : HasColimit (F ⊞ G) :=
  hasColimit_of_iso (pointwiseBiprodIso F G).symm

/-- The canonical comparison from the colimit of a pointwise binary biproduct to the binary
biproduct of the two colimits. -/
@[stacks 0A2F "colimit comparison for binary biproduct diagrams"]
noncomputable def colimitBiprodIso :
    colimit (F ⊞ G) ≅ colimit F ⊞ colimit G :=
  HasColimit.isoOfNatIso (pointwiseBiprodIso F G).symm ≪≫
    colimit.isoColimitCocone (PointwiseBiprodColimit.colimitCocone F G)

/-- Under `colimitBiprodIso`, the colimit leg at `j` is the lift of the two component colimit
legs. -/
@[reassoc]
theorem colimitBiprodIso_ι_hom (j : J) :
    colimit.ι (F ⊞ G) j ≫ (colimitBiprodIso F G).hom =
      biprod.lift
        (((biprod.fst : F ⊞ G ⟶ F).app j) ≫ colimit.ι F j)
        (((biprod.snd : F ⊞ G ⟶ G).app j) ≫ colimit.ι G j) := sorry

/-- The left projection of `colimitBiprodIso` recovers the colimit leg of the left summand. -/
@[reassoc (attr := simp)]
theorem colimitBiprodIso_hom_fst (j : J) :
    colimit.ι (F ⊞ G) j ≫ (colimitBiprodIso F G).hom ≫ biprod.fst =
      (biprod.fst : F ⊞ G ⟶ F).app j ≫ colimit.ι F j := sorry

/-- The right projection of `colimitBiprodIso` recovers the colimit leg of the right summand. -/
@[reassoc (attr := simp)]
theorem colimitBiprodIso_hom_snd (j : J) :
    colimit.ι (F ⊞ G) j ≫ (colimitBiprodIso F G).hom ≫ biprod.snd =
      (biprod.snd : F ⊞ G ⟶ G).app j ≫ colimit.ι G j := sorry

end Colimits

/-- A binary biproduct of diagrams into an idempotent-complete category admits a colimit exactly
when both summand diagrams do. -/
@[stacks 0A2F "colimits of binary biproducts of diagrams"]
theorem hasColimit_biprod_iff [IsIdempotentComplete C] :
    HasColimit (F ⊞ G) ↔ HasColimit F ∧ HasColimit G := sorry

end CategoryTheory.Limits

/- Data audit: `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
`PointwiseBiprodColimit.ι` and `PointwiseBiprodColimit.desc`.  The additional `sorryAx` reported
for `PointwiseBiprodColimit.colimitCocone` and `colimitBiprodIso` is confined to the named
naturality, universal-property, and isomorphism proof fields; their objects and morphisms are the
explicit data above. -/
