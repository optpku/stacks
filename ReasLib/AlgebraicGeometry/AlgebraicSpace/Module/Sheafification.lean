/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Modules
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

private def presentationEquiv {S : Scheme.{u}} (X : AlgebraicSpace S) :
    site X ≌ smallEtaleSite X :=
  CategoryTheory.Equivalence.mk (toPresentation X) (fromPresentation X)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; rfl))

private instance presentationEquiv_inverse_isDenseSubsite {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (presentationEquiv X).inverse.IsDenseSubsite
      (smallEtaleTopology X) (topology X) :=
  Modules.fromPresentation_isDenseSubsite X

private instance presentationOver_inverse_isDenseSubsite {S : Scheme.{u}}
    (X : AlgebraicSpace S) (U : site X) :
    (Over.postEquiv U (presentationEquiv X)).inverse.IsDenseSubsite
      ((smallEtaleTopology X).over ((presentationEquiv X).functor.obj U))
      ((topology X).over U) := sorry

/-- Abelian-group-valued presheaves on the small étale site admit left exact
sheafification in the coefficient universe. -/
instance hasSheafify {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasSheafify (topology X) AddCommGrpCat.{u} :=
  (presentationEquiv X).hasSheafify (topology X) (smallEtaleTopology X) AddCommGrpCat.{u}

/-- A morphism of abelian-group-valued presheaves on the small étale site becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
instance wEqualsLocallyBijective {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (topology X).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Abelian-group-valued presheaves on each slice of the small étale site admit left
exact sheafification in the coefficient universe. -/
instance overHasSheafify {S : Scheme.{u}} (X : AlgebraicSpace S) (U : site X) :
    HasSheafify ((topology X).over U) AddCommGrpCat.{u} := by
  -- Local instance justification (defeq pin): Transport the specified atlas-based slice
  -- reflector, with left-exactness as a law of that same reflector.
  letI : HasSheafify
      ((smallEtaleTopology X).over ((presentationEquiv X).functor.obj U))
      AddCommGrpCat.{u} :=
    { isRightAdjoint := smallEtaleOverAbelianSheafification X _
      isLeftExact := by sorry }
  exact (Over.postEquiv U (presentationEquiv X)).hasSheafify
    ((topology X).over U)
    ((smallEtaleTopology X).over ((presentationEquiv X).functor.obj U)) AddCommGrpCat.{u}

/-- A morphism of abelian-group-valued presheaves on a slice of the small étale site
becomes an isomorphism after sheafification exactly when it is locally bijective. -/
instance overWEqualsLocallyBijective {S : Scheme.{u}} (X : AlgebraicSpace S) (U : site X) :
    ((topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Abelian sheafification on a double slice is transported from the slice at its
underlying chart through the canonical iterated-slice equivalence. -/
instance overOverHasSheafify {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : site X) (V : Over U) :
    HasSheafify (((topology X).over U).over V) AddCommGrpCat.{u} :=
  V.iteratedSliceEquiv.hasSheafify (((topology X).over U).over V)
    ((topology X).over V.left) AddCommGrpCat.{u}

/-- On each double slice, abelian sheafification equivalences are precisely the locally
bijective morphisms. -/
instance overOverWEqualsLocallyBijective {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : site X) (V : Over U) :
    (((topology X).over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Forgetting rings to abelian groups preserves the sheaf condition on the small
étale site. -/
instance hasSheafComposeForget {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (topology X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u}) := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
