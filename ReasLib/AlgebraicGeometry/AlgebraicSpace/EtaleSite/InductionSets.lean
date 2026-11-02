/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Induction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.AbsoluteAffineDiagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer

/-!
# Collections for qcqs induction on the spaces-étale site

Collections of objects of `X_spaces,étale` support quasi-compact quasi-separated
induction when their members are quasi-compact and absolutely quasi-separated,
they are closed under quasi-compact opens, and they contain every affine object.
Examples arise from absolute separatedness, absolute affine-diagonality, and
quasi-compact opens of the base space or affine objects of the site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A collection of quasi-compact absolutely quasi-separated spaces-étale objects
that is closed under quasi-compact opens and contains every affine object. -/
structure QcqsSpacesEtaleInductionSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Set (spacesEtaleSite X)) : Prop where
  /-- Every member of `B` is quasi-compact. -/
  isQuasiCompact : ∀ W ∈ B, IsQuasiCompact W.left
  /-- Every member of `B` is absolutely quasi-separated. -/
  isAbsolutelyQuasiSeparated : ∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left
  /-- `B` is closed under quasi-compact open immersions in the site. -/
  mem_open : ∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
    [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B
  /-- Every affine object of the site lies in `B`. -/
  mem_affine : ∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B

/-- Construct an induction collection from quasi-compactness and absolute
quasi-separatedness of its members, closure under quasi-compact opens, and
membership of every affine object. -/
def QcqsSpacesEtaleInductionSet.of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Set (spacesEtaleSite X))
    (isQuasiCompact : ∀ W ∈ B, IsQuasiCompact W.left)
    (isAbsolutelyQuasiSeparated : ∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left)
    (mem_open : ∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
      [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B)
    (mem_affine : ∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B) :
    QcqsSpacesEtaleInductionSet B where
  isQuasiCompact := isQuasiCompact
  isAbsolutelyQuasiSeparated := isAbsolutelyQuasiSeparated
  mem_open := mem_open
  mem_affine := mem_affine

/-- The packaged conditions are exactly quasi-compactness and absolute
quasi-separatedness of members, closure under quasi-compact opens, and
membership of every affine object. -/
theorem QcqsSpacesEtaleInductionSet.spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {B : Set (spacesEtaleSite X)} (hB : QcqsSpacesEtaleInductionSet B) :
    (∀ W ∈ B, IsQuasiCompact W.left) ∧
      (∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left) ∧
      (∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
        [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B) ∧
      (∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B) :=
  ⟨hB.isQuasiCompact, hB.isAbsolutelyQuasiSeparated, hB.mem_open, hB.mem_affine⟩

/-- Quasi-compact absolutely separated objects of `X_spaces,étale`. -/
def qcAbsolutelySeparatedSpacesEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Set (spacesEtaleSite X) :=
  {W | IsQuasiCompact W.left ∧ IsAbsolutelySeparated W.left}

/-- Membership in `qcAbsolutelySeparatedSpacesEtale X` is quasi-compactness
together with absolute separatedness of the underlying algebraic space. -/
theorem mem_qcAbsolutelySeparatedSpacesEtale {S : Scheme.{u}}
    {X : AlgebraicSpace S} {W : spacesEtaleSite X} :
    W ∈ qcAbsolutelySeparatedSpacesEtale X ↔
      IsQuasiCompact W.left ∧ IsAbsolutelySeparated W.left :=
  Iff.rfl

/-- Quasi-compact objects of `X_spaces,étale` with affine diagonal over the
terminal scheme. -/
def qcAbsolutelyAffineDiagonalSpacesEtale {S : Scheme.{u}}
    (X : AlgebraicSpace S) : Set (spacesEtaleSite X) :=
  {W | IsQuasiCompact W.left ∧ IsAbsolutelyAffineDiagonal W.left}

/-- Membership in `qcAbsolutelyAffineDiagonalSpacesEtale X` is quasi-compactness
together with absolute affine-diagonality of the underlying algebraic space. -/
theorem mem_qcAbsolutelyAffineDiagonalSpacesEtale {S : Scheme.{u}}
    {X : AlgebraicSpace S} {W : spacesEtaleSite X} :
    W ∈ qcAbsolutelyAffineDiagonalSpacesEtale X ↔
      IsQuasiCompact W.left ∧ IsAbsolutelyAffineDiagonal W.left :=
  Iff.rfl

/-- Quasi-compact objects of `X_spaces,étale` that are open subspaces of `X` or
open subspaces of an affine object of the site. -/
def qcqsGeneratedSpacesEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Set (spacesEtaleSite X) :=
  {W | IsQuasiCompact W.left ∧
    (IsOpenImmersion W.hom ∨
      ∃ (V : spacesEtaleSite X) (j : W ⟶ V),
        IsAffine V.left ∧ IsOpenImmersion j.left)}

/-- Membership in `qcqsGeneratedSpacesEtale X` is quasi-compactness together with
being an open subspace of `X` or an open of an affine object of the site. -/
theorem mem_qcqsGeneratedSpacesEtale_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {W : spacesEtaleSite X} :
    W ∈ qcqsGeneratedSpacesEtale X ↔
      IsQuasiCompact W.left ∧
        (IsOpenImmersion W.hom ∨
          ∃ (V : spacesEtaleSite X) (j : W ⟶ V),
            IsAffine V.left ∧ IsOpenImmersion j.left) :=
  Iff.rfl

/-- The final object `spacesEtaleSite.self X` is a quasi-compact open subspace of
`X`, hence lies in `qcqsGeneratedSpacesEtale X`. -/
theorem self_mem_qcqsGeneratedSpacesEtale {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] :
    spacesEtaleSite.self X ∈ qcqsGeneratedSpacesEtale X :=
  by
    refine ⟨?_, Or.inl ?_⟩
    · change IsQuasiCompact X
      infer_instance
    · change IsOpenImmersion (𝟙 X)
      infer_instance

private theorem isQuasiCompact_of_isAffine {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [IsAffine Y] : IsQuasiCompact Y := by
  rcases IsAffine.exists_affineScheme (X := Y) with ⟨T, hT, ⟨e⟩⟩
  letI := hT
  let e' : Y.functorOfPoints ≅ yoneda.obj T :=
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id }
  refine ⟨⟨T, e'.inv, ?_, inferInstance, inferInstance⟩⟩
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro a b g fst snd h
  letI : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
  letI : IsIso snd := isIso_of_reflects_iso snd yoneda
  letI : IsIso snd.left := inferInstanceAs (IsIso ((Over.forget S).map snd))
  change AlgebraicGeometry.Etale snd.left
  infer_instance

private theorem isAbsolutelySeparated_of_isAffine {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [IsAffine Y] : IsAbsolutelySeparated Y := by
  rcases IsAffine.exists_affineScheme (X := Y) with ⟨T, hT, ⟨e⟩⟩
  letI := hT
  let e' : extendBaseTerminal Y ≅ ofOver ((Over.map (terminal.from S)).obj T) :=
    (extendBaseFunctor (terminal.from S)).mapIso e ≪≫
      isoOfFunctorOfPoints (extendBasePresheafYonedaIso (terminal.from S) T)
  letI : AlgebraicGeometry.IsAffine ((Over.map (terminal.from S)).obj T).left := hT
  exact ⟨IsSeparated.of_separated e'.hom⟩

private theorem isPullback_diag_of_mono {C : Type*} [Category* C]
    {F G : C} [HasBinaryProduct F F] [HasBinaryProduct G G] (f : F ⟶ G) [Mono f] :
    IsPullback f (Limits.diag F) (Limits.diag G) (prod.map f f) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (prod.diag_map f).symm
    (fun s ↦ s.snd ≫ prod.fst) ?_ ?_ ?_)
  · intro s
    simpa [Category.assoc, prod.lift_fst, prod.lift_snd] using (s.condition =≫ prod.fst).symm
  · intro s
    apply prod.hom_ext
    · simp [Limits.diag, prod.lift_fst]
    · have h₁ : (s.snd ≫ prod.fst) ≫ f = s.fst := by
        simpa [Category.assoc, prod.lift_fst, prod.lift_snd] using (s.condition =≫ prod.fst).symm
      have h₂ : (s.snd ≫ prod.snd) ≫ f = s.fst := by
        simpa [Category.assoc, prod.lift_fst, prod.lift_snd] using (s.condition =≫ prod.snd).symm
      have hs := (cancel_mono f).mp (h₁.trans h₂.symm)
      simpa [Limits.diag, Category.assoc, prod.lift_fst, prod.lift_snd] using hs
  · intro s m _ hm
    simpa [Category.assoc, prod.lift_fst, prod.lift_snd] using (hm =≫ prod.fst)

private theorem extendBasePresheafMap_mono {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [Mono f] :
    Mono (extendBasePresheafMap g f) := by
  haveI : ∀ V, Mono ((extendBasePresheafMap g f).app V) := by
    intro V
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro x y h
    rcases x with ⟨φ, x⟩
    rcases y with ⟨ψ, y⟩
    change (⟨φ, f.app _ x⟩ : Σ t : V.unop ⟶ Over.mk g,
      G.obj (Opposite.op (Over.mk t.left))) = ⟨ψ, f.app _ y⟩ at h
    have hφ : φ = ψ := congrArg Sigma.fst h
    subst ψ
    have hxy := eq_of_heq (Sigma.mk.inj h).2
    have hxy' : x = y := CategoryTheory.injective_of_mono (f.app _) hxy
    subst y
    rfl
  exact NatTrans.mono_of_mono_app _

private theorem isAbsolutelyAffineDiagonal_of_isOpenImmersion {S : Scheme.{u}}
    {U W : AlgebraicSpace S} (j : U ⟶ W) [IsOpenImmersion j]
    [IsAbsolutelyAffineDiagonal W] : IsAbsolutelyAffineDiagonal U := by
  have hmono : (MorphismProperty.monomorphisms (Over S)).presheaf
      (j : U.functorOfPoints ⟶ W.functorOfPoints) :=
    MorphismProperty.relative_monotone (F := yoneda)
      (P := MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion))
      (P' := MorphismProperty.monomorphisms (Over S)) (by
        intro A B f hf
        letI : AlgebraicGeometry.IsOpenImmersion f.left := hf
        change Mono f
        exact Over.mono_of_mono_left f) j (IsOpenImmersion.presheaf (f := j))
  letI : @Mono ((Over S)ᵒᵖ ⥤ Type u) _ U.functorOfPoints W.functorOfPoints j :=
    MorphismProperty.presheaf_monomorphisms_le_monomorphisms _ hmono
  letI := extendBasePresheafMap_mono (terminal.from S)
    (F := U.functorOfPoints) (G := W.functorOfPoints) j
  let P : MorphismProperty (Over (⊤_ Scheme.{u})) :=
    MorphismProperty.over (@AlgebraicGeometry.IsAffineHom)
  letI : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  exact ⟨MorphismProperty.of_isPullback (P := P.presheaf)
    (isPullback_diag_of_mono (extendBasePresheafMap (terminal.from S) j))
    (IsAbsolutelyAffineDiagonal.isAffineHom_diag_extendBase (X := W))⟩

/-- For quasi-compact absolutely quasi-separated `X`, the generated collection
is an induction collection. -/
theorem qcqsGeneratedSpacesEtale_isInductionSet {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    QcqsSpacesEtaleInductionSet (qcqsGeneratedSpacesEtale X) :=
  by
    refine QcqsSpacesEtaleInductionSet.of _ ?_ ?_ ?_ ?_
    · intro W hW
      exact hW.1
    · intro W hW
      rcases hW.2 with hW | ⟨V, j, hV, hj⟩
      · have hsep := @IsImmersion.separated S W.left X W.hom
          (@IsImmersion.ofIsOpenImmersion S W.left X W.hom hW)
        exact @IsAbsolutelyQuasiSeparated.of_quasiSeparated S W.left X W.hom
          inferInstance (@QuasiSeparated.of_separated S W.left X W.hom hsep)
      · letI := hV
        letI := hj
        exact IsAbsolutelyQuasiSeparated.of_quasiSeparated j.left
    · intro U W j _ _ hW
      refine ⟨inferInstance, ?_⟩
      rcases hW.2 with hW | ⟨V, k, hV, hk⟩
      · apply Or.inl
        have hcomp := @IsOpenImmersion.comp S U.left W.left X j.left W.hom
          inferInstance hW
        have hw : (j.left ≫ W.hom : U.left ⟶ X) = U.hom :=
          MorphismProperty.Over.w j
        exact hw ▸ hcomp
      · letI := hk
        refine Or.inr ⟨V, j ≫ k, hV, ?_⟩
        change IsOpenImmersion (j.left ≫ k.left)
        infer_instance
    · intro V _
      refine ⟨isQuasiCompact_of_isAffine V.left, Or.inr ⟨V, 𝟙 V, inferInstance, ?_⟩⟩
      change IsOpenImmersion (𝟙 V.left)
      infer_instance

/-- The generated collection is contained in every induction collection that
contains the identity object of the spaces-étale site. -/
theorem qcqsGeneratedSpacesEtale_subset {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {B : Set (spacesEtaleSite X)} (h_self : spacesEtaleSite.self X ∈ B)
    (hB : QcqsSpacesEtaleInductionSet B) :
    qcqsGeneratedSpacesEtale X ⊆ B :=
  by
    intro W hW
    rcases hW with ⟨hqc, hW | ⟨V, j, hV, hj⟩⟩
    · letI := hqc
      letI := hW
      letI : IsOpenImmersion (spacesEtaleSite.homToSelf W).left := by
        change IsOpenImmersion W.hom
        exact hW
      exact hB.mem_open (spacesEtaleSite.homToSelf W) h_self
    · letI := hqc
      letI := hV
      letI := hj
      exact hB.mem_open j (hB.mem_affine V)

/-- For quasi-compact absolutely separated `X`, the quasi-compact absolutely
separated site objects form an induction collection containing the identity object. -/
theorem qcAbsolutelySeparatedSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelySeparated X] :
    spacesEtaleSite.self X ∈ qcAbsolutelySeparatedSpacesEtale X ∧
      QcqsSpacesEtaleInductionSet (qcAbsolutelySeparatedSpacesEtale X) := by
  refine ⟨?_, QcqsSpacesEtaleInductionSet.of _ ?_ ?_ ?_ ?_⟩
  · change IsQuasiCompact X ∧ IsAbsolutelySeparated X
    exact ⟨inferInstance, inferInstance⟩
  · intro W hW
    exact hW.1
  · intro W hW
    letI := hW.2
    infer_instance
  · intro U W j _ _ hW
    letI := hW.2
    exact ⟨inferInstance, IsAbsolutelySeparated.of_separated j.left⟩
  · intro V _
    exact ⟨isQuasiCompact_of_isAffine V.left, isAbsolutelySeparated_of_isAffine V.left⟩

/-- For quasi-compact `X` with absolute affine diagonal, the quasi-compact site
objects with absolute affine diagonal form an induction collection containing
the identity object. -/
theorem qcAbsolutelyAffineDiagonalSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyAffineDiagonal X] :
    spacesEtaleSite.self X ∈ qcAbsolutelyAffineDiagonalSpacesEtale X ∧
      QcqsSpacesEtaleInductionSet (qcAbsolutelyAffineDiagonalSpacesEtale X) := by
  refine ⟨?_, QcqsSpacesEtaleInductionSet.of _ ?_ ?_ ?_ ?_⟩
  · change IsQuasiCompact X ∧ IsAbsolutelyAffineDiagonal X
    exact ⟨inferInstance, inferInstance⟩
  · intro W hW
    exact hW.1
  · intro W hW
    letI := hW.2
    infer_instance
  · intro U W j _ _ hW
    letI := hW.2
    exact ⟨inferInstance, isAbsolutelyAffineDiagonal_of_isOpenImmersion j.left⟩
  · intro V _
    exact ⟨isQuasiCompact_of_isAffine V.left, inferInstance⟩

/-- For quasi-compact absolutely quasi-separated `X`, the quasi-compact opens of
`X` and of affine site objects form the smallest induction collection containing
the identity object. -/
theorem qcqsGeneratedSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    qcqsGeneratedSpacesEtale X =
      sInf {B | spacesEtaleSite.self X ∈ B ∧ QcqsSpacesEtaleInductionSet B} :=
  by
    apply le_antisymm
    · apply le_sInf
      intro B hB
      exact qcqsGeneratedSpacesEtale_subset X hB.1 hB.2
    · exact sInf_le ⟨self_mem_qcqsGeneratedSpacesEtale X,
        qcqsGeneratedSpacesEtale_isInductionSet X⟩

/-- A property holding on affine objects and preserved by elementary distinguished
squares with quasi-compact absolutely separated target, quasi-compact open part,
and affine étale part holds on all quasi-compact absolutely separated site objects. -/
theorem qcqsSpacesEtale_induction_of_absolutelySeparated {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelySeparated X]
    (P : spacesEtaleSite X → Prop)
    (h_affine : ∀ (W : spacesEtaleSite X) [IsAffine W.left], P W)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [Etale f.left]
      [IsQuasiCompact W.left] [IsAbsolutelySeparated W.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      P U → P V → P (spacesEtaleSite.fiber j f) → P W)
    (W : spacesEtaleSite X) [IsQuasiCompact W.left] [IsAbsolutelySeparated W.left] :
    P W :=
  by
    let hB := (qcAbsolutelySeparatedSpacesEtale_spec X).2
    refine qcqsSpacesEtale_induction_mem X (qcAbsolutelySeparatedSpacesEtale X) P
      hB.isQuasiCompact hB.isAbsolutelyQuasiSeparated hB.mem_open hB.mem_affine
      h_affine ?_ W ?_
    · intro U V W j f _ _ _ _ hW hU hV hUV
      letI := hW.1
      letI := hW.2
      exact h_square j f hU hV hUV
    · exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace
