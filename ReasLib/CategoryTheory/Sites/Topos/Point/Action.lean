module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import ReasLib.CategoryTheory.Sites.Action.JointlySurjective
public import ReasLib.CategoryTheory.Sites.Action.LeftRegular

/-!
# The forgetful point of the jointly-surjective action site

This module provides the canonical point of the jointly-surjective site on `G`-actions.  The
elementary left-regular action constructions are owned separately by `Action.LeftRegular`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v

namespace Action

noncomputable section

variable (G : Type u) [Monoid G]

/-- The distinguished left-regular element in the category of elements of the forgetful
functor on `G`-sets. -/
noncomputable abbrev forgetElementsBase : (Action.forget (Type u) G).Elements :=
  (Action.forget (Type u) G).elementsMk (Action.leftRegular G) ((1 : G) : G)

/-- The left-regular generator is initial in the category of elements of the forgetful functor
on `G`-sets. -/
noncomputable def forgetElementsBaseInitial : IsInitial (forgetElementsBase G) :=
  @IsInitial.ofUnique _ _ (forgetElementsBase G)
    (fun Y ↦
      { default := ⟨leftRegularOrbitHom G Y.2, sorry⟩
        uniq := sorry })

/-- The opposite of the left-regular generator in the opposite element category. -/
noncomputable abbrev forgetElementsBaseTerminalObj :
    (Action.forget (Type u) G).Elementsᵒᵖ :=
  op (forgetElementsBase G)

/-- The opposite left-regular generator is terminal in the opposite element category. -/
noncomputable def forgetElementsBaseTerminal : IsTerminal (forgetElementsBaseTerminalObj G) :=
  terminalOpOfInitial (forgetElementsBaseInitial G)

/-- The category of elements of the forgetful functor on `G`-sets has an initial object. -/
theorem forgetElements_hasInitial :
    Limits.HasInitial (Functor.Elements (Action.forget (Type u) G)) := sorry

/-- The category of elements of the forgetful functor on `G`-sets is initially small. -/
instance forgetElements_initiallySmall :
    InitiallySmall.{u} (Functor.Elements (Action.forget (Type u) G)) := sorry

/-- Covering sieves in the jointly-surjective topology act jointly surjectively on the
forgetful fiber functor. -/
theorem forget_jointlySurjective
    {X : Action (Type u) G} (R : Sieve X)
    (hR : R ∈ Action.jointlySurjectiveTopology G X) (x : X.V) :
    ∃ (Y : Action (Type u) G) (f : Y ⟶ X), R f ∧
      ∃ y : Y.V, (Action.forget (Type u) G).map f y = x := sorry

/-- The covering-lift condition for the forgetful fiber functor in the constructor form for a
point of the jointly-surjective site. -/
theorem forgetfulPoint_jointlySurjective :
    ∀ {X : Action (Type u) G}, ∀ R ∈ Action.jointlySurjectiveTopology G X,
      ∀ x : (Action.forget (Type u) G).obj X,
        ∃ (Y : Action (Type u) G) (f : Y ⟶ X), ∃ (_ : R.arrows f),
          ∃ y : (Action.forget (Type u) G).obj Y,
            (Action.forget (Type u) G).map f y = x := sorry

/-- Example 7.33.7 (00YF) (1): the forgetful functor on `G`-sets defines a canonical point of
the jointly-surjective site. -/
@[stacks 00YF "(1)"]
noncomputable def forgetfulPoint : (Action.jointlySurjectiveTopology G).Point where
  fiber := Action.forget (Type u) G
  isCofiltered := Functor.isCofiltered_elements (Action.forget (Type u) G)
  initiallySmall := forgetElements_initiallySmall G
  jointly_surjective := forgetfulPoint_jointlySurjective G

/-- The presheaf fiber at the forgetful point is evaluation on the left regular `G`-action. -/
noncomputable def forgetfulPoint_presheafFiberObjIso_leftRegular
    (P : (Action (Type u) G)ᵒᵖ ⥤ Type u) :
    (forgetfulPoint G).presheafFiber.obj P ≅ P.obj (op (Action.leftRegular G)) :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((CategoryOfElements.π (forgetfulPoint G).fiber).op ⋙ P))
    (colimitOfDiagramTerminal (forgetElementsBaseTerminal G)
      ((CategoryOfElements.π (forgetfulPoint G).fiber).op ⋙ P))

/-- The left-regular evaluation comparison is natural in the presheaf. -/
theorem forgetfulPoint_presheafFiberObjIso_leftRegular_naturality
    {P Q : (Action (Type u) G)ᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    (forgetfulPoint G).presheafFiber.map f ≫
        (forgetfulPoint_presheafFiberObjIso_leftRegular G Q).hom =
      (forgetfulPoint_presheafFiberObjIso_leftRegular G P).hom ≫
        ((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G))).map f := sorry

/-- The sheaf fiber at the forgetful point is evaluation on the left regular `G`-action. -/
noncomputable def forgetfulPoint_sheafFiberIso_leftRegular :
    (forgetfulPoint G).sheafFiber ≅
      sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u) ⋙
        (evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G)) :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u))
    (NatIso.ofComponents (fun P ↦ forgetfulPoint_presheafFiberObjIso_leftRegular G P)
      (fun f ↦ forgetfulPoint_presheafFiberObjIso_leftRegular_naturality G f))

end

end Action
