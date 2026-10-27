/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Stability
public import ReasLib.CategoryTheory.Functor.FullyFaithful.Source
public import ReasLib.CategoryTheory.Functor.FullyFaithful.Target
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computing Derived Values from Endpoint Full Faithfulness

For a localization functor, full faithfulness on the hom-sets ending at one object makes the
identity right denominator terminal.  The sourcewise dual makes the identity left denominator
initial.  These endpoint conditions are exactly what injective and projective objects provide;
global full faithfulness of the localization is unnecessary.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

namespace RightDerived.IdentityDenominator

variable {F : D ⥤ D'} {S : MorphismProperty D} {X : D}

private noncomputable def terminalIdentity (hQ : S.Q.FullyFaithfulTo X) :
    IsTerminal (CostructuredArrow.mk (𝟙 (S.Q.obj X))) :=
  IsTerminal.ofUniqueHom
    (fun j ↦ CostructuredArrow.homMk (hQ.preimage j.hom) (by
      change S.Q.map (hQ.preimage j.hom) ≫ 𝟙 _ = j.hom
      rw [Category.comp_id, hQ.map_preimage]))
    (fun j f ↦ by
      apply CostructuredArrow.hom_ext
      apply hQ.homEquiv.injective
      change S.Q.map f.left = S.Q.map (hQ.preimage j.hom)
      rw [hQ.map_preimage]
      have hf := CostructuredArrow.w f
      change S.Q.map f.left ≫ 𝟙 _ = j.hom at hf
      simpa only [Category.comp_id] using hf)

/-- Targetwise full faithfulness of the localization makes the right-derived indexing diagram
essentially constant. -/
@[stacks 05S9 "terminal identity denominator"]
theorem isEssentiallyConstant (hQ : S.Q.FullyFaithfulTo X) :
    IsFiltered.IsEssentiallyConstant
      (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) := by
  let M := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let i : CostructuredArrow S.Q (S.Q.obj X) := CostructuredArrow.mk (𝟙 _)
  let hi := terminalIdentity hQ
  refine ⟨coconeOfDiagramTerminal hi M, i,
    { section_ := 𝟙 _
      id := ?_ }, ?_⟩
  · change 𝟙 (M.obj i) ≫ M.map (hi.from i) = 𝟙 _
    rw [Category.id_comp, hi.from_self, M.map_id]
  · intro j
    refine ⟨i, 𝟙 i, hi.from j, ?_⟩
    change M.map (hi.from j) = M.map (hi.from j) ≫ 𝟙 (M.obj i) ≫ M.map (𝟙 i)
    rw [M.map_id, Category.id_comp, Category.comp_id]

/-- Targetwise full faithfulness of the localization makes the right-derived value source-defined
at the chosen object. -/
@[stacks 05S9 "terminal identity denominator"]
theorem definedAt (hQ : S.Q.FullyFaithfulTo X) :
    RightDerived.DefinedAt F S X :=
  ⟨isEssentiallyConstant hQ⟩

/-- A terminal identity denominator supplies Mathlib's pointwise right-derived existence
predicate. -/
@[stacks 05S9 "terminal identity denominator"]
theorem hasPointwise (hQ : S.Q.FullyFaithfulTo X) :
    F.HasPointwiseRightDerivedFunctorAt S X := by
  let M := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  exact ⟨HasColimit.mk ⟨coconeOfDiagramTerminal (terminalIdentity hQ) M,
    colimitOfDiagramTerminal (terminalIdentity hQ) M⟩⟩

/-- The identity-denominator leg into a pointwise right-derived value is an isomorphism under
targetwise full faithfulness. -/
@[stacks 05SX "terminal identity denominator"]
theorem isIso_valueLeg [S.ContainsIdentities] (hQ : S.Q.FullyFaithfulTo X)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    IsIso (CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 X) (S.id_mem X)) := by
  change IsIso (colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)
    (CostructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)))
  rw [Localization.isoOfHom_id_inv]
  exact (colimit.isColimit _).isIso_ι_app_of_isTerminal _ (terminalIdentity hQ)

/-- A terminal identity denominator makes the chosen object compute every pointwise
right-derived value. -/
@[stacks 05SX "terminal identity denominator"]
theorem computesAt [S.ContainsIdentities] (hQ : S.Q.FullyFaithfulTo X) :
    RightDerived.ComputesAt F S X := by
  letI := hasPointwise (F := F) hQ
  exact { toDefinedAt := definedAt hQ, isIso_valueLeg := isIso_valueLeg hQ }

end RightDerived.IdentityDenominator

namespace LeftDerived.IdentityDenominator

variable {F : D ⥤ D'} {S : MorphismProperty D} {X : D}

private noncomputable def initialIdentity (hQ : S.Q.FullyFaithfulFrom X) :
    IsInitial (StructuredArrow.mk (𝟙 (S.Q.obj X))) :=
  IsInitial.ofUniqueHom
    (fun j ↦ StructuredArrow.homMk (hQ.preimage j.hom) (by
      change 𝟙 _ ≫ S.Q.map (hQ.preimage j.hom) = j.hom
      rw [Category.id_comp, hQ.map_preimage]))
    (fun j f ↦ by
      apply StructuredArrow.hom_ext
      apply hQ.homEquiv.injective
      change S.Q.map f.right = S.Q.map (hQ.preimage j.hom)
      rw [hQ.map_preimage]
      have hf := StructuredArrow.w f
      change 𝟙 _ ≫ S.Q.map f.right = j.hom at hf
      simpa only [Category.id_comp] using hf)

/-- Sourcewise full faithfulness of the localization makes the left-derived indexing diagram
essentially constant. -/
@[stacks 05S9 "initial identity denominator"]
theorem isEssentiallyConstant (hQ : S.Q.FullyFaithfulFrom X) :
    IsCofiltered.IsEssentiallyConstant
      (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) := by
  let M := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let i : StructuredArrow (S.Q.obj X) S.Q := StructuredArrow.mk (𝟙 _)
  let hi := initialIdentity hQ
  refine ⟨coneOfDiagramInitial hi M, i,
    { retraction := 𝟙 _
      id := ?_ }, ?_⟩
  · change M.map (hi.to i) ≫ 𝟙 (M.obj i) = 𝟙 _
    rw [Category.comp_id, hi.to_self, M.map_id]
  · intro j
    refine ⟨i, 𝟙 i, hi.to j, ?_⟩
    change M.map (hi.to j) = M.map (𝟙 i) ≫ 𝟙 (M.obj i) ≫ M.map (hi.to j)
    rw [M.map_id, Category.id_comp, Category.id_comp]

/-- Sourcewise full faithfulness of the localization makes the left-derived value source-defined
at the chosen object. -/
@[stacks 05S9 "initial identity denominator"]
theorem definedAt (hQ : S.Q.FullyFaithfulFrom X) :
    LeftDerived.DefinedAt F S X :=
  ⟨isEssentiallyConstant hQ⟩

/-- An initial identity denominator supplies Mathlib's pointwise left-derived existence
predicate. -/
@[stacks 05S9 "initial identity denominator"]
theorem hasPointwise (hQ : S.Q.FullyFaithfulFrom X) :
    F.HasPointwiseLeftDerivedFunctorAt S X := by
  let M := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  exact ⟨HasLimit.mk ⟨coneOfDiagramInitial (initialIdentity hQ) M,
    limitOfDiagramInitial (initialIdentity hQ) M⟩⟩

/-- The identity-denominator projection from a pointwise left-derived value is an isomorphism
under sourcewise full faithfulness. -/
@[stacks 05SX "initial identity denominator"]
theorem isIso_valueProjection [S.ContainsIdentities] (hQ : S.Q.FullyFaithfulFrom X)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    IsIso (CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 X) (S.id_mem X)) := by
  change IsIso (limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
    (StructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)))
  rw [Localization.isoOfHom_id_inv]
  exact (limit.isLimit _).isIso_π_app_of_isInitial _ (initialIdentity hQ)

/-- An initial identity denominator makes the chosen object compute every pointwise left-derived
value. -/
@[stacks 05SX "initial identity denominator"]
theorem computesAt [S.ContainsIdentities] (hQ : S.Q.FullyFaithfulFrom X) :
    LeftDerived.ComputesAt F S X := by
  letI := hasPointwise (F := F) hQ
  exact { toDefinedAt := definedAt hQ, isIso_valueProjection := isIso_valueProjection hQ }

end LeftDerived.IdentityDenominator


end CategoryTheory.Functor
