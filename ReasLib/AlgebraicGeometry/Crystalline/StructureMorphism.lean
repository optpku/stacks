/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.Sheafification

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- The site functor sending a crystalline object over `X` to its source over `S` by
postcomposition with `x₀ ≫ I.subschemeι`. -/
noncomputable def bigStructureFunctor {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    RelativeCRIS S I γ h_compatible X x₀ ⥤ Over S :=
  crystallineForgetful S I γ h_compatible s X x₀ h_p ⋙
    Scheme.Zariski.Big.map (x₀ ≫ I.subschemeι)

/-- The structure functor is objectwise the source object `U` over `X` postcomposed to `S`. -/
theorem bigStructureFunctor_obj {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (c : RelativeCRIS S I γ h_compatible X x₀) :
    (bigStructureFunctor S I γ h_compatible s X x₀ h_p).obj c =
      Over.mk (c.1.source.hom ≫ x₀ ≫ I.subschemeι) := sorry

/-- The structure functor factors through `Over X` and the intermediate closed subscheme. -/
theorem bigStructureFunctor_factorization {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    bigStructureFunctor S I γ h_compatible s X x₀ h_p =
      crystallineForgetful S I γ h_compatible s X x₀ h_p ⋙
        Scheme.Zariski.Big.map x₀ ⋙
          Scheme.Zariski.Big.map I.subschemeι := sorry

/-- The site functor defining the big crystalline structure morphism is cocontinuous. -/
instance bigStructureFunctor_isCocontinuous {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    (bigStructureFunctor S I γ h_compatible s X x₀ h_p).IsCocontinuous
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      S.bigZariskiTopology := sorry


/-- The morphism from the big crystalline topos of `X/S` to the big Zariski topos of `S`
induced by the cocontinuous functor sending a crystalline object to its source over `S`. -/
noncomputable def bigStructureMorphism {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn S.bigZariskiTopology
      (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  (bigStructureFunctor S I γ h_compatible s X x₀ h_p).morphismOfTopoiInOfCocontinuous
    (crystallineZariskiTopology S I γ h_compatible X x₀) S.bigZariskiTopology

section Compatibilities

variable {p : ℕ} [Fact (Nat.Prime p)] (B B' : Base.{u} p)
variable (f : B.source ⟶ B'.source)
variable (g : DividedPowerSchemeHom B.ideal B'.ideal B.toSpec B'.toSpec)
variable (h_comm : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
variable (h_dividedPowers_compatible :
  ∀ (V : B'.scheme.affineOpens) (W : B.scheme.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (B'.dividedPowers V).IsDPMorphism (B.dividedPowers W) (g.base.appLE V W hVW).hom)

/-- Taking the source over the base commutes with crystalline change of base,
via the identity isomorphisms of the underlying source schemes. -/
def bigStructureFunctor_mapFunctorIso :
    bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent ⋙ Zariski.Big.map g.base ≅
      mapFunctor (h_compatible := B.compatible) (h'_compatible := B'.compatible)
        f g.base g.zeroFiberMap g.zeroFiber_comm h_comm h_dividedPowers_compatible
        B.toSpec B'.toSpec g.base_over g.ideal_compatible B.prime_nilpotent B'.prime_nilpotent ⋙
      bigStructureFunctor B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.toSpec
        B'.source B'.sourceToClosed B'.prime_nilpotent :=
  NatIso.ofComponents
    (fun A => Over.isoMk (Iso.refl A.1.source.left) (by
      change 𝟙 _ ≫ ((A.1.source.hom ≫ f) ≫
          (B'.sourceToClosed ≫ B'.ideal.subschemeι)) =
        (A.1.source.hom ≫ (B.sourceToClosed ≫ B.ideal.subschemeι)) ≫ g.base
      simp only [Category.id_comp, Category.assoc]
      rw [← Category.assoc f, h_comm, Category.assoc B.sourceToClosed,
        g.zeroFiber_comm]))
    (fun φ => by
      apply Over.OverMorphism.ext
      change φ.source.left ≫ 𝟙 _ = 𝟙 _ ≫ φ.source.left
      simp only [Category.comp_id, Category.id_comp])

/-- The source-scheme map of the structure-functor comparison is the identity. -/
@[simp] theorem bigStructureFunctor_mapFunctorIso_hom_app_left
    (A : RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed) :
    ((bigStructureFunctor_mapFunctorIso B B' f g h_comm h_dividedPowers_compatible).hom.app A).left =
      𝟙 A.1.source.left := rfl

variable [HasSheafify
  (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed) (Type (u + 1))]
variable [HasSheafify
  (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed) (Type (u + 1))]
variable [∀ P : (RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
    B.source B.sourceToClosed B.prime_nilpotent).op.HasPointwiseRightKanExtension P]
variable [∀ P : (RelativeCRIS B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (bigStructureFunctor B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.toSpec
    B'.source B'.sourceToClosed B'.prime_nilpotent).op.HasPointwiseRightKanExtension P]

/-- The inverse images of the big crystalline structure morphisms commute with
crystalline functoriality up to a canonical natural isomorphism. This concerns
underlying topoi: the analogous ringed claim for the source-object structure functor
fails, since it would require maps from functions on `U` to functions on its
thickening `T`, including an impossible unital ring map `𝔽₃ → ℤ/9ℤ`. -/
def crystallineToposHom_bigStructureMorphismIso :
    (Zariski.Big.morphismOfTopoi g.base).inverseImage ⋙
        (bigStructureMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent).inverseImage ≅
      (bigStructureMorphism B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.toSpec
          B'.source B'.sourceToClosed B'.prime_nilpotent).inverseImage ⋙
        (functorialToposHom B B' f g h_comm h_dividedPowers_compatible).inverseImage := by
  let bX := bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
    B.source B.sourceToClosed B.prime_nilpotent
  let bY := bigStructureFunctor B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.toSpec
    B'.source B'.sourceToClosed B'.prime_nilpotent
  let F := mapFunctor (h_compatible := B.compatible) (h'_compatible := B'.compatible)
    f g.base g.zeroFiberMap g.zeroFiber_comm h_comm h_dividedPowers_compatible
    B.toSpec B'.toSpec g.base_over g.ideal_compatible B.prime_nilpotent B'.prime_nilpotent
  let J := crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed
  let K := crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed
  let forget := sheafToPresheaf B'.scheme.bigZariskiTopology (Type (u + 1))
  let preX := (Functor.whiskeringLeft _ _ (Type (u + 1))).obj bX.op
  let preY := (Functor.whiskeringLeft _ _ (Type (u + 1))).obj bY.op
  let preF := (Functor.whiskeringLeft _ _ (Type (u + 1))).obj F.op
  let aX := presheafToSheaf J (Type (u + 1))
  let aY := presheafToSheaf K (Type (u + 1))
  exact
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Zariski.Big.map g.base).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (u + 1)) B.scheme.bigZariskiTopology B'.scheme.bigZariskiTopology)
      (preX ⋙ aX) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft forget
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((bX.op.whiskeringLeftObjCompIso (Zariski.Big.map g.base).op).symm ≪≫
            (Functor.whiskeringLeft _ _ (Type (u + 1))).mapIso
              (NatIso.op (bigStructureFunctor_mapFunctorIso B B' f g h_comm
                h_dividedPowers_compatible)).symm ≪≫
            F.op.whiskeringLeftObjCompIso bY.op) aX ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator forget preY (preF ⋙ aX)).symm ≪≫
    Functor.isoWhiskerLeft (forget ⋙ preY)
      (show preF ⋙ aX ≅ aY ⋙ F.sheafPullbackCocontinuous (Type (u + 1)) J K from
        Functor.CocontinuousPullback.sheafificationCompatibility.{u + 1, u + 1, u, u, u + 1}
          F J K) ≪≫
    (Functor.associator (forget ⋙ preY) aY
      (F.sheafPullbackCocontinuous (Type (u + 1)) J K)).symm

end Compatibilities

end AlgebraicGeometry.Scheme.Crystalline

end
