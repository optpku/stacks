/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AdicSpfSquare
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Composition

/-!
# Rig-surjective morphisms of formal algebraic spaces

A locally of finite type morphism of locally Noetherian formal algebraic spaces
is rig-surjective when every adic test map from the formal spectrum of a complete
discrete valuation ring lifts after an extension of complete discrete valuation
rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Let `S` be a scheme, and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Assume that `X` and `Y` are locally Noetherian
and that `f` is locally of finite type. We say `f` is rig-surjective if for every
solid diagram of an adic morphism `p : Spf(R) ⟶ Y` from a complete discrete
valuation ring `R` there exists an extension of complete discrete valuation rings
`R ⊂ R'` and a morphism `Spf(R') ⟶ X` making the displayed triangle commute. -/
@[mk_iff]
class RigSurjective {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] : Prop where
  /-- Every solid adic `Spf` square admits an extension of complete discrete
  valuation rings together with a lift `Spf(R') ⟶ X`. -/
  exists_extension : ∀ sq : AdicSpfSquare f, Nonempty sq.Extension

namespace RigSurjective

private theorem exists_extension_of_lift {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (sq : AdicSpfSquare f)
    (lift : sq.specSpf ⟶ X) (fac : lift ≫ f = sq.p) : Nonempty sq.Extension := by
  letI := sq.commRing
  letI := sq.domain
  letI := sq.discreteValuationRing
  letI := sq.completeLocalRing
  letI : IsExtensionOfDiscreteValuationRings sq.R sq.R :=
    { toIsLocalHom := ⟨fun _ h ↦ h⟩
      algebraMap_injective := fun _ _ h ↦ h }
  exact ⟨AdicSpfSquare.Extension.of sq sq.R
    (spfMap sq.R sq.R sq.structureHom ≫ lift) (by rw [Category.assoc, fac])⟩

/-- The identity morphism of a locally Noetherian formal algebraic space is
rig-surjective. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] : RigSurjective (𝟙 X) where
  exists_extension sq := exists_extension_of_lift sq sq.p (Category.comp_id sq.p)

/-- A locally of finite type morphism of locally Noetherian formal algebraic
spaces is rig-surjective if and only if every adic complete-DVR test map lifts
after an extension of complete discrete valuation rings. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    RigSurjective f ↔ ∀ sq : AdicSpfSquare f, Nonempty sq.Extension := by
  constructor
  · intro h
    exact h.exists_extension
  · intro h
    exact ⟨h⟩

/-- A locally of finite type monomorphism of locally Noetherian formal algebraic
spaces is rig-surjective if and only if every adic morphism from the formal
spectrum of a complete discrete valuation ring factors through its source,
without extending the test ring. -/
theorem iff_adicSpf_factors {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f] :
    RigSurjective f ↔
      ∀ sq : AdicSpfSquare f, ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p := by
  constructor
  · sorry
  · intro h
    constructor
    intro sq
    obtain ⟨lift, fac⟩ := h sq
    exact exists_extension_of_lift sq lift fac

/-- In a pullback square of locally Noetherian formal algebraic spaces, the
base-change leg of a rig-surjective morphism is rig-surjective when the two
original morphisms and the base-change leg are locally of finite type. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [RigSurjective f] [LocallyOfFiniteType snd] :
    RigSurjective snd where
  exists_extension test := by
    let test' : AdicSpfSquare f :=
      { test with
        p := test.p ≫ g
        h_adic := AlgebraicSpace.representableByAlgebraicSpaces.comp _ _ test.h_adic
          (LocallyOfFiniteType.representable (f := g)) }
    obtain ⟨e⟩ := RigSurjective.exists_extension (f := f) test'
    have fac : e.lift ≫ f = (e.verticalMap ≫ test.p) ≫ g := by
      simpa only [Category.assoc] using e.fac
    exact ⟨{ e with
      lift := sq.lift e.lift (e.verticalMap ≫ test.p) fac
      fac := sq.lift_snd e.lift (e.verticalMap ≫ test.p) fac }⟩

/-- The base change of a rig-surjective morphism along a locally of finite type
morphism of locally Noetherian formal algebraic spaces is rig-surjective. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [RigSurjective f] :
    RigSurjective (pullback.snd f g) := by
  exact of_isPullback (IsPullback.of_hasPullback f g)

/-- If the composite of two locally of finite type morphisms of locally
Noetherian formal algebraic spaces is rig-surjective, then the second morphism
is rig-surjective. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [RigSurjective (f ≫ g)] :
    RigSurjective g where
  exists_extension sq := by
    let sq' : AdicSpfSquare (f ≫ g) := { sq with }
    obtain ⟨e⟩ := RigSurjective.exists_extension (f := f ≫ g) sq'
    exact ⟨{ e with
      lift := e.lift ≫ f
      fac := by simpa only [Category.assoc] using e.fac }⟩

/-- The composite of two locally of finite type rig-surjective morphisms of
locally Noetherian formal algebraic spaces is rig-surjective. -/
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [RigSurjective f] [RigSurjective g] : RigSurjective (f ≫ g) :=
  sorry

/-- If the composite of two locally of finite type morphisms of locally
Noetherian formal algebraic spaces is rig-surjective and the second morphism
is a monomorphism, then the first morphism is rig-surjective. -/
theorem of_comp_mono {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [RigSurjective (f ≫ g)] [Mono g] :
    RigSurjective f where
  exists_extension sq := by
    let sq' : AdicSpfSquare (f ≫ g) :=
      { sq with
        p := sq.p ≫ g
        h_adic := AlgebraicSpace.representableByAlgebraicSpaces.comp _ _ sq.h_adic
          (LocallyOfFiniteType.representable (f := g)) }
    obtain ⟨e⟩ := RigSurjective.exists_extension (f := f ≫ g) sq'
    exact ⟨{ e with
      fac := (cancel_mono g).mp (by simpa only [Category.assoc] using e.fac) }⟩

end RigSurjective

end AlgebraicGeometry.FormalAlgebraicSpace
