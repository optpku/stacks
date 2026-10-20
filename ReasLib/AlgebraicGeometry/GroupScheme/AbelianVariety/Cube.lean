module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.TheoremOfCube
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Invertible.Closed
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.AbelianVariety

/-- An invertible module on the base point `Spec k` is trivial because the Picard group of a
field spectrum is trivial. -/
lemma basePointModuleIsTrivial {k : Type u} [Field k]
    (M : (Spec (CommRingCat.of k)).Modules) [Scheme.Modules.Invertible M] :
    RingedSpace.IsTrivial M := by
  let X : Scheme := Spec (CommRingCat.of k)
  have hclass : Scheme.Modules.picardClass M = (0 : X.PicardGroup) :=
    Subsingleton.elim _ _
  exact (Scheme.PicardGroup.picardClass_eq_zero_iff (X := X) M).mp hclass

/-- Pulling back a trivial module from the base point remains trivial. -/
private lemma pullbackBasePointModuleIsTrivial {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec
    (CommRingCat.of k)) (M : (Spec (CommRingCat.of k)).Modules)
    [Scheme.Modules.Invertible M] :
    RingedSpace.IsTrivial ((Scheme.Modules.pullback f).obj M) := by
  rcases basePointModuleIsTrivial (k := k) M with ⟨e⟩
  exact ⟨(Scheme.Modules.pullback f).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso f⟩

/-- Triviality of `N ⊗ P` transfers across an isomorphism `M ≅ N`. -/
private lemma isTrivialTensorRightOfIso {X : Scheme.{u}} {M N P : X.Modules} (e : M ≅ N)
    (h : RingedSpace.IsTrivial (N ⊗ P)) :
    RingedSpace.IsTrivial (M ⊗ P) := by
  rcases h with ⟨t⟩
  exact ⟨(tensorRight P).mapIso e ≪≫ t⟩

/-- Triviality transfers across an isomorphism of module sheaves. -/
private lemma isTrivialOfIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (h : RingedSpace.IsTrivial N) : RingedSpace.IsTrivial M := by
  -- Replace the source module by the trivial target through the chosen isomorphism.
  rcases h with ⟨t⟩
  exact ⟨e ≪≫ t⟩

/-- The tensor product of two trivial module sheaves is trivial. -/
private lemma isTrivialTensor {X : Scheme.{u}} {M N : X.Modules}
    (hM : RingedSpace.IsTrivial M) (hN : RingedSpace.IsTrivial N) :
    RingedSpace.IsTrivial (M ⊗ N) := by
  -- First replace `M` by the monoidal unit, then identify `𝟙 ⊗ N` with `N`.
  rcases hM with ⟨eM⟩
  have hOneTensor : RingedSpace.IsTrivial ((𝟙_ X.Modules) ⊗ N) := by
    exact isTrivialOfIso (λ_ N) hN
  exact isTrivialOfIso ((tensorRight N).mapIso eM) hOneTensor

/-- Equal composites induce canonically isomorphic iterated pullbacks of a module sheaf. -/
private noncomputable def pullbackPullbackIsoOfCompEq
    {X Y Z : Scheme.{u}} (s : X ⟶ Y) (f g : Y ⟶ Z) (M : Z.Modules)
    (h : s ≫ f = s ≫ g) :
    ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback f).obj M)) ≅
      ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g).obj M)) :=
  -- Compare both iterated pullbacks through the common pullback along the equal composite.
  (Scheme.Modules.pullbackComp s f).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp s g).app M).symm

/-- If a restricted left-hand tensor factors as a trivial module tensored with the restricted
right-hand tensor, then the restricted cube bundle is trivial. -/
private lemma cubeRestrictionIsTrivialOfFactorization
    {X Y : Scheme.{u}} (f : X ⟶ Y) {lhs rhs : Y.Modules} {C : X.Modules}
    [Scheme.Modules.Invertible rhs] [Closed rhs]
    (e : (Scheme.Modules.pullback f).obj lhs ≅
      C ⊗ (Scheme.Modules.pullback f).obj rhs)
    (hC : RingedSpace.IsTrivial C) :
    RingedSpace.IsTrivial
      ((Scheme.Modules.pullback f).obj (lhs ⊗ ((ihom rhs).obj (𝟙_ Y.Modules)))) := by
  let rhsDual := (Scheme.Modules.pullback f).obj ((ihom rhs).obj (𝟙_ Y.Modules))
  -- Pull back the evaluation map of the invertible module to trivialize the residual factor.
  have hRhsDual : RingedSpace.IsTrivial (((Scheme.Modules.pullback f).obj rhs) ⊗ rhsDual) := by
    let j : MonoidalCategory.isInvertibleObject.inverse rhs ≅
        ((ihom rhs).obj (𝟙_ Y.Modules)) :=
      MonoidalClosed.RightInverse.isoIhomUnit rhs
        (MonoidalCategory.isInvertibleObject.inverse rhs)
        (MonoidalCategory.isInvertibleObject.tensorInverseIso rhs)
    let heval : rhs ⊗ ((ihom rhs).obj (𝟙_ Y.Modules)) ≅ 𝟙_ Y.Modules :=
      (Iso.refl rhs ⊗ᵢ j.symm) ≪≫
        MonoidalCategory.isInvertibleObject.tensorInverseIso rhs
    refine ⟨?_⟩
    exact
      (Scheme.Modules.pullbackTensorIso f rhs ((ihom rhs).obj (𝟙_ Y.Modules))).symm ≪≫
        (Scheme.Modules.pullback f).mapIso heval ≪≫
          Scheme.Modules.pullbackUnitIso f
  -- After reassociating, the factorization exposes a tensor of two trivial modules.
  have hFactored :
      RingedSpace.IsTrivial
        (((C ⊗ (Scheme.Modules.pullback f).obj rhs) ⊗ rhsDual)) := by
    apply isTrivialOfIso (α_ C ((Scheme.Modules.pullback f).obj rhs) rhsDual)
    exact isTrivialTensor hC hRhsDual
  have hTensor :
      RingedSpace.IsTrivial
        (((Scheme.Modules.pullback f).obj lhs) ⊗ rhsDual) :=
    isTrivialTensorRightOfIso e hFactored
  -- The pullback of the cube bundle is the tensor of the restricted left-hand side with the
  -- pulled-back internal Hom.
  exact
    isTrivialOfIso
      (Scheme.Modules.pullbackTensorIso f lhs ((ihom rhs).obj (𝟙_ Y.Modules)))
      hTensor

/-- On the first section face, the first coordinate restricts to the identity section. -/
private lemma cubeFirstSectionFirstCoordinate {k : Type u} [Field k]
    (A : SchemeOverField k) [GrpObj A] [AbelianVariety A]
    (σ : SplitEpi A.hom) :
    Scheme.TripleProduct.firstSection A.hom A.hom A.hom σ ≫
        Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
        Limits.pullback.fst A.hom A.hom =
      (Limits.pullback.fst A.hom A.hom ≫ A.hom) ≫ σ.section_ := by
  -- Expand the first pullback projection and then identify the induced section on `A × A`.
  have hfst :
      Scheme.TripleProduct.firstSection A.hom A.hom A.hom σ ≫
          Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
          Limits.pullback.fst A.hom A.hom =
        (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackSnd A.hom).section_) ≫
          Limits.pullback.fst A.hom A.hom := by
    simpa [Category.assoc] using
      congrArg
        (fun f : Limits.pullback A.hom A.hom ⟶ Limits.pullback A.hom A.hom ↦
          f ≫ Limits.pullback.fst A.hom A.hom)
        (Scheme.TripleProduct.firstSection_fst A.hom A.hom A.hom σ)
  have hsection :
      (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackSnd A.hom).section_) ≫
          Limits.pullback.fst A.hom A.hom =
        (Limits.pullback.fst A.hom A.hom ≫ A.hom) ≫ σ.section_ := by
    calc
      (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackSnd A.hom).section_) ≫
            Limits.pullback.fst A.hom A.hom =
          Limits.pullback.fst A.hom A.hom ≫
            ((σ.pullbackSnd A.hom).section_ ≫ Limits.pullback.fst A.hom A.hom) := by
              simp [Category.assoc]
      _ = Limits.pullback.fst A.hom A.hom ≫ (A.hom ≫ σ.section_) := by
            rw [CategoryTheory.SplitEpi.pullbackSnd_section_fst σ A.hom]
      _ = (Limits.pullback.fst A.hom A.hom ≫ A.hom) ≫ σ.section_ := by
            simp [Category.assoc]
  calc
    Scheme.TripleProduct.firstSection A.hom A.hom A.hom σ ≫
          Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
          Limits.pullback.fst A.hom A.hom =
        (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackSnd A.hom).section_) ≫
          Limits.pullback.fst A.hom A.hom := hfst
    _ = (Limits.pullback.fst A.hom A.hom ≫ A.hom) ≫ σ.section_ := hsection

/-- On the second section face, the second coordinate restricts to the identity section. -/
private lemma cubeSecondSectionSecondCoordinate {k : Type u} [Field k]
    (A : SchemeOverField k) [GrpObj A] [AbelianVariety A]
    (σ : SplitEpi A.hom) :
    Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ ≫
        Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
        Limits.pullback.snd A.hom A.hom =
      (Limits.pullback.fst A.hom A.hom ≫ A.hom) ≫ σ.section_ := by
  -- Expand the first pullback projection and then identify the induced section on `A × A`.
  have hfst :
      Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ ≫
          Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
          Limits.pullback.snd A.hom A.hom =
        (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackFst A.hom).section_) ≫
          Limits.pullback.snd A.hom A.hom := by
    simpa [Category.assoc] using
      congrArg
        (fun f : Limits.pullback A.hom A.hom ⟶ Limits.pullback A.hom A.hom ↦
          f ≫ Limits.pullback.snd A.hom A.hom)
        (Scheme.TripleProduct.secondSection_fst A.hom A.hom A.hom σ)
  have hsection :
      (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackFst A.hom).section_) ≫
          Limits.pullback.snd A.hom A.hom =
        (Limits.pullback.fst A.hom A.hom ≫ A.hom) ≫ σ.section_ := by
    calc
      (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackFst A.hom).section_) ≫
            Limits.pullback.snd A.hom A.hom =
          Limits.pullback.fst A.hom A.hom ≫
            ((σ.pullbackFst A.hom).section_ ≫ Limits.pullback.snd A.hom A.hom) := by
              simp [Category.assoc]
      _ = Limits.pullback.fst A.hom A.hom ≫ (A.hom ≫ σ.section_) := by
            rw [CategoryTheory.SplitEpi.pullbackFst_section_snd σ A.hom]
      _ = (Limits.pullback.fst A.hom A.hom ≫ A.hom) ≫ σ.section_ := by
            simp [Category.assoc]
  calc
    Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ ≫
          Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
          Limits.pullback.snd A.hom A.hom =
        (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackFst A.hom).section_) ≫
          Limits.pullback.snd A.hom A.hom := hfst
    _ = (Limits.pullback.fst A.hom A.hom ≫ A.hom) ≫ σ.section_ := hsection

/-- For an invertible module on an abelian variety, the tensor product of its pullbacks along
the triple sum and the three projections is isomorphic to the tensor product of its pullbacks
along the three pairwise sums. -/
theorem cubeIso {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A]
    [AbelianVariety A] (L : A.left.Modules) [Scheme.Modules.Invertible L] :
    let T := (A ⊗ A) ⊗ A
    let m₁ : T ⟶ A := fst (A ⊗ A) A ≫ fst A A
    let m₂ : T ⟶ A := fst (A ⊗ A) A ≫ snd A A
    let m₃ : T ⟶ A := snd (A ⊗ A) A
    let m₁₂ := m₁ * m₂
    let m₁₃ := m₁ * m₃
    let m₂₃ := m₂ * m₃
    let m₁₂₃ := m₁₂ * m₃
    let pullbackModule (m : T ⟶ A) := (Scheme.Modules.pullback m.left).obj L
    let lhs :=
      pullbackModule m₁₂₃ ⊗
        (pullbackModule m₁ ⊗ (pullbackModule m₂ ⊗ pullbackModule m₃))
    let rhs :=
      pullbackModule m₁₂ ⊗ (pullbackModule m₁₃ ⊗ pullbackModule m₂₃)
    Nonempty (lhs ≅ rhs) := by
  dsimp
  let T := (A ⊗ A) ⊗ A
  let B := A ⊗ A
  let m₁ : T ⟶ A := fst (A ⊗ A) A ≫ fst A A
  let m₂ : T ⟶ A := fst (A ⊗ A) A ≫ snd A A
  let m₃ : T ⟶ A := snd (A ⊗ A) A
  let m₁₂ := m₁ * m₂
  let m₁₃ := m₁ * m₃
  let m₂₃ := m₂ * m₃
  let m₁₂₃ := m₁₂ * m₃
  let pullbackModule (m : T ⟶ A) := (Scheme.Modules.pullback m.left).obj L
  let lhs :=
    pullbackModule m₁₂₃ ⊗
      (pullbackModule m₁ ⊗ (pullbackModule m₂ ⊗ pullbackModule m₃))
  let rhs :=
    pullbackModule m₁₂ ⊗ (pullbackModule m₁₃ ⊗ pullbackModule m₂₃)
  have hInvCube : Scheme.Modules.Invertible (lhs ⊗ ((ihom rhs).obj (𝟙_ T.left.Modules))) := by
    -- The cube bundle is a tensor product of invertible modules.
    exact MonoidalCategory.isInvertibleObject.tensor lhs
      ((ihom rhs).obj (𝟙_ T.left.Modules))
  let σ : SplitEpi A.hom :=
    { section_ := η[A].left
      id := by simpa using Over.w η[A] }
  let z : A.left := η[A].left (IsLocalRing.closedPoint k)
  have h_first :
      RingedSpace.IsTrivial
        ((Scheme.Modules.pullback
          (Scheme.TripleProduct.firstSection A.hom A.hom A.hom σ)).obj
          (lhs ⊗ ((ihom rhs).obj (𝟙_ T.left.Modules)))) := by
    -- Route correction: keep the face calculations in `SchemeOverField k` long enough to
    -- collapse the `m₁` factor to the unit morphism, and only then project to scheme maps
    -- for the pullback-transport step.
    let s₁ : B ⟶ T := Over.homMk (Scheme.TripleProduct.firstSection A.hom A.hom A.hom σ) <| by
      -- The first face still lies over `Spec k` because its third coordinate is the
      -- second projection `B ⟶ A`.
      have hs₁_hom :
          Scheme.TripleProduct.firstSection A.hom A.hom A.hom σ ≫
              Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
                Limits.pullback.fst A.hom A.hom ≫ A.hom =
            Limits.pullback.fst A.hom A.hom ≫ A.hom := by
        simpa [Category.assoc, σ.id] using
          congrArg (fun f ↦ f ≫ A.hom) (cubeFirstSectionFirstCoordinate A σ)
      simpa [T, B, m₁] using hs₁_hom
    have hm₁_one : s₁ ≫ m₁ = 1 := by
      -- On the first face, the first coordinate is the identity section.
      apply Over.OverMorphism.ext
      change
        Scheme.TripleProduct.firstSection A.hom A.hom A.hom σ ≫
            Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
            Limits.pullback.fst A.hom A.hom =
          (1 : B ⟶ A).left
      simpa [m₁, B, Hom.one_def] using cubeFirstSectionFirstCoordinate A σ
    have hm₁₂ : s₁ ≫ m₁₂ = s₁ ≫ m₂ := by
      -- Multiplication by the unit collapses the `m₁₂` factor to `m₂`.
      calc
        s₁ ≫ m₁₂ = (s₁ ≫ m₁) * (s₁ ≫ m₂) := by
          rw [MonObj.comp_mul]
        _ = s₁ ≫ m₂ := by
          rw [hm₁_one]
          simp
    have hm₁₃ : s₁ ≫ m₁₃ = s₁ ≫ m₃ := by
      -- The same unit reduction collapses the `m₁₃` factor to `m₃`.
      calc
        s₁ ≫ m₁₃ = (s₁ ≫ m₁) * (s₁ ≫ m₃) := by
          rw [MonObj.comp_mul]
        _ = s₁ ≫ m₃ := by
          rw [hm₁_one]
          simp
    have hm₁₂₃ : s₁ ≫ m₁₂₃ = s₁ ≫ m₂₃ := by
      -- After the first collapse, the remaining product is exactly `m₂₃`.
      calc
        s₁ ≫ m₁₂₃ = (s₁ ≫ m₁₂) * (s₁ ≫ m₃) := by
          rw [MonObj.comp_mul]
        _ = (s₁ ≫ m₂) * (s₁ ≫ m₃) := by
          rw [hm₁₂]
        _ = s₁ ≫ m₂₃ := by
          rw [MonObj.comp_mul]
    let R₁₂ := (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁₂)
    let R₁₃ := (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁₃)
    let R₂₃ := (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₂₃)
    let C₁ := (Scheme.Modules.pullback B.hom).obj ((Scheme.Modules.pullback η[A].left).obj L)
    have e₁₂₃ :
        (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁₂₃) ≅ R₂₃ := by
      -- Project the collapsed face equation to scheme maps before comparing iterated pullbacks.
      exact pullbackPullbackIsoOfCompEq s₁.left m₁₂₃.left m₂₃.left L
        (congrArg Over.Hom.left hm₁₂₃)
    have e₁ :
        (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁) ≅ C₁ := by
      -- The `m₁` factor is the pullback of the base-point module.
      have hm₁_left : s₁.left ≫ m₁.left = B.hom ≫ η[A].left := by
        simpa [Hom.one_def] using congrArg Over.Hom.left hm₁_one
      exact
        (Scheme.Modules.pullbackComp s₁.left m₁.left).app L ≪≫
          (Scheme.Modules.pullbackCongr hm₁_left).app L ≪≫
            ((Scheme.Modules.pullbackComp B.hom η[A].left).app L).symm
    have e₁₂ :
        (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₂) ≅ R₁₂ := by
      exact pullbackPullbackIsoOfCompEq s₁.left m₂.left m₁₂.left L
        (congrArg Over.Hom.left hm₁₂).symm
    have e₁₃ :
        (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₃) ≅ R₁₃ := by
      exact pullbackPullbackIsoOfCompEq s₁.left m₃.left m₁₃.left L
        (congrArg Over.Hom.left hm₁₃).symm
    have hInvEta :
        Scheme.Modules.Invertible ((Scheme.Modules.pullback (Over.Hom.left η[A])).obj L) := by
      simpa using (Scheme.Modules.pullback_isInvertible (f := η[A].left) L)
    have hC₁ : RingedSpace.IsTrivial C₁ := by
      -- Pulling back the base-point module along `B ⟶ Spec k` stays trivial.
      exact
        @pullbackBasePointModuleIsTrivial
          _ _ _ B.hom ((Scheme.Modules.pullback η[A].left).obj L) hInvEta
    have rhsFactor :
        (Scheme.Modules.pullback s₁.left).obj rhs ≅ R₁₂ ⊗ (R₁₃ ⊗ R₂₃) := by
      -- Expand the restricted right-hand tensor into its three factor pullbacks.
      calc
        (Scheme.Modules.pullback s₁.left).obj rhs
            ≅
              (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁₂) ⊗
                (Scheme.Modules.pullback s₁.left).obj
                  (pullbackModule m₁₃ ⊗ pullbackModule m₂₃) := by
              simpa [rhs] using
                (Scheme.Modules.pullbackTensorIso s₁.left
                  (pullbackModule m₁₂)
                  (pullbackModule m₁₃ ⊗ pullbackModule m₂₃))
        _ ≅ R₁₂ ⊗
              ((Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁₃) ⊗
                (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₂₃)) := by
              simpa [R₁₂] using
                (Iso.refl ((Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁₂)) ⊗ᵢ
                  (Scheme.Modules.pullbackTensorIso s₁.left
                    (pullbackModule m₁₃) (pullbackModule m₂₃)))
        _ ≅ R₁₂ ⊗ (R₁₃ ⊗ R₂₃) := by
              simpa [R₁₃, R₂₃] using
                (Iso.refl
                  (R₁₂ ⊗
                    ((Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁₃) ⊗
                      (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₂₃))))
    have lhsFactor :
        (Scheme.Modules.pullback s₁.left).obj lhs ≅ R₂₃ ⊗ (C₁ ⊗ (R₁₂ ⊗ R₁₃)) := by
      -- Expand the restricted left-hand tensor and rewrite each factor using the face data.
      calc
        (Scheme.Modules.pullback s₁.left).obj lhs
            ≅
              (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁₂₃) ⊗
                (Scheme.Modules.pullback s₁.left).obj
                  (pullbackModule m₁ ⊗
                    (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [lhs] using
                (Scheme.Modules.pullbackTensorIso s₁.left
                  (pullbackModule m₁₂₃)
                  (pullbackModule m₁ ⊗
                    (pullbackModule m₂ ⊗ pullbackModule m₃)))
        _ ≅ R₂₃ ⊗
              (Scheme.Modules.pullback s₁.left).obj
                (pullbackModule m₁ ⊗
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [R₂₃] using
                (e₁₂₃ ⊗ᵢ
                  Iso.refl
                    ((Scheme.Modules.pullback s₁.left).obj
                      (pullbackModule m₁ ⊗
                        (pullbackModule m₂ ⊗ pullbackModule m₃))))
        _ ≅ R₂₃ ⊗
              ((Scheme.Modules.pullback s₁.left).obj (pullbackModule m₁) ⊗
                (Scheme.Modules.pullback s₁.left).obj
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa using
                (Iso.refl R₂₃ ⊗ᵢ
                  (Scheme.Modules.pullbackTensorIso s₁.left
                    (pullbackModule m₁)
                    (pullbackModule m₂ ⊗ pullbackModule m₃)))
        _ ≅ R₂₃ ⊗
              (C₁ ⊗
                (Scheme.Modules.pullback s₁.left).obj
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [C₁] using
                (Iso.refl R₂₃ ⊗ᵢ
                  (e₁ ⊗ᵢ
                    Iso.refl
                      ((Scheme.Modules.pullback s₁.left).obj
                        (pullbackModule m₂ ⊗ pullbackModule m₃))))
        _ ≅ R₂₃ ⊗
              (C₁ ⊗
                ((Scheme.Modules.pullback s₁.left).obj (pullbackModule m₂) ⊗
                  (Scheme.Modules.pullback s₁.left).obj (pullbackModule m₃))) := by
              simpa [Category.assoc] using
                (Iso.refl R₂₃ ⊗ᵢ
                  (Iso.refl C₁ ⊗ᵢ
                    (Scheme.Modules.pullbackTensorIso s₁.left
                      (pullbackModule m₂) (pullbackModule m₃))))
        _ ≅ R₂₃ ⊗ (C₁ ⊗ (R₁₂ ⊗ R₁₃)) := by
              simpa [R₁₂, R₁₃] using
                (Iso.refl R₂₃ ⊗ᵢ (Iso.refl C₁ ⊗ᵢ (e₁₂ ⊗ᵢ e₁₃)))
    have tensorAssembly :
        R₂₃ ⊗ (C₁ ⊗ (R₁₂ ⊗ R₁₃)) ≅ C₁ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := by
      -- A short braiding/associator chain puts the trivial factor on the left and restores
      -- the right-hand tensor spelling.
      calc
        R₂₃ ⊗ (C₁ ⊗ (R₁₂ ⊗ R₁₃))
            ≅ (R₂₃ ⊗ C₁) ⊗ (R₁₂ ⊗ R₁₃) := (α_ R₂₃ C₁ (R₁₂ ⊗ R₁₃)).symm
        _ ≅ (C₁ ⊗ R₂₃) ⊗ (R₁₂ ⊗ R₁₃) := (β_ R₂₃ C₁) ⊗ᵢ Iso.refl _
        _ ≅ C₁ ⊗ (R₂₃ ⊗ (R₁₂ ⊗ R₁₃)) := α_ C₁ R₂₃ (R₁₂ ⊗ R₁₃)
        _ ≅ C₁ ⊗ ((R₂₃ ⊗ R₁₂) ⊗ R₁₃) := Iso.refl _ ⊗ᵢ (α_ R₂₃ R₁₂ R₁₃).symm
        _ ≅ C₁ ⊗ ((R₁₂ ⊗ R₂₃) ⊗ R₁₃) := Iso.refl _ ⊗ᵢ ((β_ R₂₃ R₁₂) ⊗ᵢ Iso.refl _)
        _ ≅ C₁ ⊗ (R₁₂ ⊗ (R₂₃ ⊗ R₁₃)) := Iso.refl _ ⊗ᵢ (α_ R₁₂ R₂₃ R₁₃)
        _ ≅ C₁ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := Iso.refl _ ⊗ᵢ (Iso.refl _ ⊗ᵢ β_ R₂₃ R₁₃)
    have factorization :
        (Scheme.Modules.pullback s₁.left).obj lhs ≅
          C₁ ⊗ (Scheme.Modules.pullback s₁.left).obj rhs := by
      -- Combine the factorwise transports with the monoidal assembly and then fold the
      -- restricted right-hand side back into `s₁^* rhs`.
      calc
        (Scheme.Modules.pullback s₁.left).obj lhs
            ≅ R₂₃ ⊗ (C₁ ⊗ (R₁₂ ⊗ R₁₃)) := lhsFactor
        _ ≅ C₁ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := tensorAssembly
        _ ≅ C₁ ⊗ (Scheme.Modules.pullback s₁.left).obj rhs := by
              exact (tensorLeft C₁).mapIso rhsFactor.symm
    -- The generic factorization-to-triviality lemma now closes the first face.
    exact cubeRestrictionIsTrivialOfFactorization s₁.left factorization hC₁
  have h_second :
      RingedSpace.IsTrivial
        ((Scheme.Modules.pullback
          (Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ)).obj
          (lhs ⊗ ((ihom rhs).obj (𝟙_ T.left.Modules)))) := by
    -- Route correction: the second face is the same calculation with the unit now sitting in the
    -- second coordinate, so the constant factor comes from `m₂`.
    let s₂ : B ⟶ T := Over.homMk (Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ) <| by
      -- The second face still lies over `Spec k` because its first coordinate is the
      -- first projection `B ⟶ A`.
      have hs₂_hom :
          Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ ≫
              Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
                Limits.pullback.fst A.hom A.hom ≫ A.hom =
            Limits.pullback.fst A.hom A.hom ≫ A.hom := by
        have hs₂_fst :
            Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ ≫
                Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
                  Limits.pullback.fst A.hom A.hom =
              Limits.pullback.fst A.hom A.hom := by
          calc
            Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ ≫
                  Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
                  Limits.pullback.fst A.hom A.hom =
                (Limits.pullback.fst A.hom A.hom ≫ (σ.pullbackFst A.hom).section_) ≫
                  Limits.pullback.fst A.hom A.hom := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun f ↦ f ≫ Limits.pullback.fst A.hom A.hom)
                        (Scheme.TripleProduct.secondSection_fst A.hom A.hom A.hom σ)
            _ = Limits.pullback.fst A.hom A.hom := by
                  simp [Category.assoc, (σ.pullbackFst A.hom).id]
        simpa [Category.assoc] using congrArg (fun f ↦ f ≫ A.hom) hs₂_fst
      simpa [T, B, m₁] using hs₂_hom
    have hm₂_one : s₂ ≫ m₂ = 1 := by
      -- On the second face, the second coordinate is the identity section.
      apply Over.OverMorphism.ext
      change
        Scheme.TripleProduct.secondSection A.hom A.hom A.hom σ ≫
            Limits.pullback.fst (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom ≫
            Limits.pullback.snd A.hom A.hom =
          (1 : B ⟶ A).left
      simpa [m₂, B, Hom.one_def] using cubeSecondSectionSecondCoordinate A σ
    have hm₁₂ : s₂ ≫ m₁₂ = s₂ ≫ m₁ := by
      -- Multiplication by the unit collapses the `m₁₂` factor to `m₁`.
      calc
        s₂ ≫ m₁₂ = (s₂ ≫ m₁) * (s₂ ≫ m₂) := by
          rw [MonObj.comp_mul]
        _ = s₂ ≫ m₁ := by
          rw [hm₂_one]
          simp
    have hm₂₃ : s₂ ≫ m₂₃ = s₂ ≫ m₃ := by
      -- The same unit reduction collapses the `m₂₃` factor to `m₃`.
      calc
        s₂ ≫ m₂₃ = (s₂ ≫ m₂) * (s₂ ≫ m₃) := by
          rw [MonObj.comp_mul]
        _ = s₂ ≫ m₃ := by
          rw [hm₂_one]
          simp
    have hm₁₂₃ : s₂ ≫ m₁₂₃ = s₂ ≫ m₁₃ := by
      -- After the second collapse, the remaining product is exactly `m₁₃`.
      calc
        s₂ ≫ m₁₂₃ = (s₂ ≫ m₁₂) * (s₂ ≫ m₃) := by
          rw [MonObj.comp_mul]
        _ = (s₂ ≫ m₁) * (s₂ ≫ m₃) := by
          rw [hm₁₂]
        _ = s₂ ≫ m₁₃ := by
          rw [MonObj.comp_mul]
    let R₁₂ := (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁₂)
    let R₁₃ := (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁₃)
    let R₂₃ := (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₂₃)
    let C₂ := (Scheme.Modules.pullback B.hom).obj ((Scheme.Modules.pullback η[A].left).obj L)
    have e₁₂₃ :
        (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁₂₃) ≅ R₁₃ := by
      exact pullbackPullbackIsoOfCompEq s₂.left m₁₂₃.left m₁₃.left L
        (congrArg Over.Hom.left hm₁₂₃)
    have e₁ :
        (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁) ≅ R₁₂ := by
      exact pullbackPullbackIsoOfCompEq s₂.left m₁.left m₁₂.left L
        (congrArg Over.Hom.left hm₁₂).symm
    have e₂ :
        (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₂) ≅ C₂ := by
      have hm₂_left : s₂.left ≫ m₂.left = B.hom ≫ η[A].left := by
        simpa [Hom.one_def] using congrArg Over.Hom.left hm₂_one
      exact
        (Scheme.Modules.pullbackComp s₂.left m₂.left).app L ≪≫
          (Scheme.Modules.pullbackCongr hm₂_left).app L ≪≫
            ((Scheme.Modules.pullbackComp B.hom η[A].left).app L).symm
    have e₃ :
        (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₃) ≅ R₂₃ := by
      exact pullbackPullbackIsoOfCompEq s₂.left m₃.left m₂₃.left L
        (congrArg Over.Hom.left hm₂₃).symm
    have hInvEta :
        Scheme.Modules.Invertible ((Scheme.Modules.pullback (Over.Hom.left η[A])).obj L) := by
      simpa using (Scheme.Modules.pullback_isInvertible (f := η[A].left) L)
    have hC₂ : RingedSpace.IsTrivial C₂ := by
      -- The same base-point pullback trivializes the constant `m₂` factor.
      exact
        @pullbackBasePointModuleIsTrivial
          _ _ _ B.hom ((Scheme.Modules.pullback η[A].left).obj L) hInvEta
    have rhsFactor :
        (Scheme.Modules.pullback s₂.left).obj rhs ≅ R₁₂ ⊗ (R₁₃ ⊗ R₂₃) := by
      -- Expand the restricted right-hand tensor into its three factor pullbacks.
      calc
        (Scheme.Modules.pullback s₂.left).obj rhs
            ≅
              (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁₂) ⊗
                (Scheme.Modules.pullback s₂.left).obj
                  (pullbackModule m₁₃ ⊗ pullbackModule m₂₃) := by
              simpa [rhs] using
                (Scheme.Modules.pullbackTensorIso s₂.left
                  (pullbackModule m₁₂)
                  (pullbackModule m₁₃ ⊗ pullbackModule m₂₃))
        _ ≅ R₁₂ ⊗
              ((Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁₃) ⊗
                (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₂₃)) := by
              simpa [R₁₂] using
                (Iso.refl ((Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁₂)) ⊗ᵢ
                  (Scheme.Modules.pullbackTensorIso s₂.left
                    (pullbackModule m₁₃) (pullbackModule m₂₃)))
        _ ≅ R₁₂ ⊗ (R₁₃ ⊗ R₂₃) := by
              simpa [R₁₃, R₂₃] using
                (Iso.refl
                  (R₁₂ ⊗
                    ((Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁₃) ⊗
                      (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₂₃))))
    have lhsFactor :
        (Scheme.Modules.pullback s₂.left).obj lhs ≅ R₁₃ ⊗ (R₁₂ ⊗ (C₂ ⊗ R₂₃)) := by
      -- Expand the restricted left-hand tensor and rewrite each factor using the face data.
      calc
        (Scheme.Modules.pullback s₂.left).obj lhs
            ≅
              (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁₂₃) ⊗
                (Scheme.Modules.pullback s₂.left).obj
                  (pullbackModule m₁ ⊗
                    (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [lhs] using
                (Scheme.Modules.pullbackTensorIso s₂.left
                  (pullbackModule m₁₂₃)
                  (pullbackModule m₁ ⊗
                    (pullbackModule m₂ ⊗ pullbackModule m₃)))
        _ ≅ R₁₃ ⊗
              (Scheme.Modules.pullback s₂.left).obj
                (pullbackModule m₁ ⊗
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [R₁₃] using
                (e₁₂₃ ⊗ᵢ
                  Iso.refl
                    ((Scheme.Modules.pullback s₂.left).obj
                      (pullbackModule m₁ ⊗
                        (pullbackModule m₂ ⊗ pullbackModule m₃))))
        _ ≅ R₁₃ ⊗
              ((Scheme.Modules.pullback s₂.left).obj (pullbackModule m₁) ⊗
                (Scheme.Modules.pullback s₂.left).obj
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa using
                (Iso.refl R₁₃ ⊗ᵢ
                  (Scheme.Modules.pullbackTensorIso s₂.left
                    (pullbackModule m₁)
                    (pullbackModule m₂ ⊗ pullbackModule m₃)))
        _ ≅ R₁₃ ⊗
              (R₁₂ ⊗
                (Scheme.Modules.pullback s₂.left).obj
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [R₁₂] using
                (Iso.refl R₁₃ ⊗ᵢ
                  (e₁ ⊗ᵢ
                    Iso.refl
                      ((Scheme.Modules.pullback s₂.left).obj
                        (pullbackModule m₂ ⊗ pullbackModule m₃))))
        _ ≅ R₁₃ ⊗
              (R₁₂ ⊗
                ((Scheme.Modules.pullback s₂.left).obj (pullbackModule m₂) ⊗
                  (Scheme.Modules.pullback s₂.left).obj (pullbackModule m₃))) := by
              simpa [Category.assoc] using
                (Iso.refl R₁₃ ⊗ᵢ
                  (Iso.refl R₁₂ ⊗ᵢ
                    (Scheme.Modules.pullbackTensorIso s₂.left
                      (pullbackModule m₂) (pullbackModule m₃))))
        _ ≅ R₁₃ ⊗ (R₁₂ ⊗ (C₂ ⊗ R₂₃)) := by
              simpa [C₂, R₂₃] using
                (Iso.refl R₁₃ ⊗ᵢ (Iso.refl R₁₂ ⊗ᵢ (e₂ ⊗ᵢ e₃)))
    have tensorAssembly :
        R₁₃ ⊗ (R₁₂ ⊗ (C₂ ⊗ R₂₃)) ≅ C₂ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := by
      -- Move the trivial factor from the middle to the front by a braiding/associator chain.
      calc
        R₁₃ ⊗ (R₁₂ ⊗ (C₂ ⊗ R₂₃))
            ≅ (R₁₃ ⊗ R₁₂) ⊗ (C₂ ⊗ R₂₃) := (α_ R₁₃ R₁₂ (C₂ ⊗ R₂₃)).symm
        _ ≅ (R₁₂ ⊗ R₁₃) ⊗ (C₂ ⊗ R₂₃) := (β_ R₁₃ R₁₂) ⊗ᵢ Iso.refl _
        _ ≅ R₁₂ ⊗ (R₁₃ ⊗ (C₂ ⊗ R₂₃)) := α_ R₁₂ R₁₃ (C₂ ⊗ R₂₃)
        _ ≅ R₁₂ ⊗ ((R₁₃ ⊗ C₂) ⊗ R₂₃) := Iso.refl _ ⊗ᵢ (α_ R₁₃ C₂ R₂₃).symm
        _ ≅ R₁₂ ⊗ ((C₂ ⊗ R₁₃) ⊗ R₂₃) := Iso.refl _ ⊗ᵢ ((β_ R₁₃ C₂) ⊗ᵢ Iso.refl _)
        _ ≅ R₁₂ ⊗ (C₂ ⊗ (R₁₃ ⊗ R₂₃)) := Iso.refl _ ⊗ᵢ (α_ C₂ R₁₃ R₂₃)
        _ ≅ (R₁₂ ⊗ C₂) ⊗ (R₁₃ ⊗ R₂₃) := (α_ R₁₂ C₂ (R₁₃ ⊗ R₂₃)).symm
        _ ≅ (C₂ ⊗ R₁₂) ⊗ (R₁₃ ⊗ R₂₃) := (β_ R₁₂ C₂) ⊗ᵢ Iso.refl _
        _ ≅ C₂ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := α_ C₂ R₁₂ (R₁₃ ⊗ R₂₃)
    have factorization :
        (Scheme.Modules.pullback s₂.left).obj lhs ≅
          C₂ ⊗ (Scheme.Modules.pullback s₂.left).obj rhs := by
      -- Assemble the transported factors and refold the restricted right-hand side.
      calc
        (Scheme.Modules.pullback s₂.left).obj lhs
            ≅ R₁₃ ⊗ (R₁₂ ⊗ (C₂ ⊗ R₂₃)) := lhsFactor
        _ ≅ C₂ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := tensorAssembly
        _ ≅ C₂ ⊗ (Scheme.Modules.pullback s₂.left).obj rhs := by
              exact (tensorLeft C₂).mapIso rhsFactor.symm
    -- The generic factorization-to-triviality lemma now closes the second face.
    exact cubeRestrictionIsTrivialOfFactorization s₂.left factorization hC₂
  have h_fibre :
      RingedSpace.IsTrivial
        ((Scheme.Modules.pullback
          ((Limits.pullback.snd (Limits.pullback.fst A.hom A.hom ≫ A.hom) A.hom).fiberι z)).obj
          (lhs ⊗ ((ihom rhs).obj (𝟙_ T.left.Modules)))) := by
    -- Route correction: first normalize the fibre source as a `Spec k`-scheme and identify the
    -- third coordinate with the unit section; only then do the same factorwise pullback transport
    -- and tensor assembly as on the two section faces.
    let sf : (m₃.left).fiber z ⟶ T.left := (m₃.left).fiberι z
    let sfToBase : (m₃.left).fiber z ⟶ Spec (CommRingCat.of k) :=
      (m₃.left).fiberToSpecResidueField z ≫
        Spec.map (CommRingCat.ofHom (Scheme.Hom.ResidueField.mapOfSpec A.hom z))
    have hSpecMapMapOfSpec :
        Spec.map (CommRingCat.ofHom (Scheme.Hom.ResidueField.mapOfSpec A.hom z)) =
          A.left.fromSpecResidueField z ≫ A.hom := by
      let y : Spec (CommRingCat.of k) := A.hom z
      -- Rewrite the canonical `k`-algebra on `κ(z)` through the residue-field point map.
      change
        Spec.map
            (CommRingCat.ofHom
              (((A.hom.residueFieldMap z).hom).comp
                (((Scheme.Spec.residueFieldIso (CommRingCat.of k) y).inv).hom.comp
                  (algebraMap k y.asIdeal.ResidueField)))) =
          A.left.fromSpecResidueField z ≫ A.hom
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp]
      rw [Spec.map_comp, Spec.map_comp]
      simp only [CommRingCat.ofHom_hom]
      calc
        Spec.map (Scheme.Hom.residueFieldMap A.hom z) ≫
            Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of k) y).inv ≫
              Spec.map (CommRingCat.ofHom (algebraMap k y.asIdeal.ResidueField)) =
          Spec.map (Scheme.Hom.residueFieldMap A.hom z) ≫
              (Spec (CommRingCat.of k)).fromSpecResidueField y := by
            have hbase :=
              Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
                (R := CommRingCat.of k) (x := y)
            simpa [Category.assoc] using
              congrArg (fun g ↦ Spec.map (Scheme.Hom.residueFieldMap A.hom z) ≫ g) hbase
        _ = A.left.fromSpecResidueField z ≫ A.hom := by
            simpa [y] using
              (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := A.hom) z)
    have hFromSpecUnit :
        A.left.fromSpecResidueField z =
          Spec.map (CommRingCat.ofHom (Scheme.Hom.ResidueField.mapOfSpec A.hom z)) ≫
            η[A].left := by
      -- TODO: identify the `Spec κ(z)`-valued unit point through `SpecToEquivOfField`.
      -- The remaining blocker is the residue-field component: prove that both
      -- `A.left.fromSpecResidueField z` and
      -- `Spec.map (CommRingCat.ofHom (Scheme.Hom.ResidueField.mapOfSpec A.hom z)) ≫ η[A].left`
      -- induce the identity embedding of `κ(z)` after the required `residueFieldCongr` transport.
      sorry
    let S₃ : SchemeOverField k := Over.mk sfToBase
    let s₃ : S₃ ⟶ T := Over.homMk sf <| by
      -- The structure map of the fibre source is the canonical `Spec k`-valued map of the point
      -- `z`, written through `mapOfSpec`.
      calc
        sf ≫ T.hom = sf ≫ (m₃.left ≫ A.hom) := by
          simpa [Category.assoc] using congrArg (fun g ↦ sf ≫ g) (Over.w m₃).symm
        _ = (m₃.left).fiberToSpecResidueField z ≫ (A.left.fromSpecResidueField z ≫ A.hom) := by
            simpa [sf, Category.assoc] using
              (Scheme.Hom.fiber_fac_assoc (f := m₃.left) (y := z) (h := A.hom))
        _ = sfToBase := by
            rw [← hSpecMapMapOfSpec]
            rfl
    have hm₃_one : s₃ ≫ m₃ = 1 := by
      -- The fibre of the third coordinate is the unit section above the base point `z`.
      apply Over.OverMorphism.ext
      change sf ≫ m₃.left = sfToBase ≫ η[A].left
      calc
        sf ≫ m₃.left = (m₃.left).fiberToSpecResidueField z ≫ A.left.fromSpecResidueField z := by
          simpa [sf] using (Scheme.Hom.fiber_fac (f := m₃.left) (y := z))
        _ = (m₃.left).fiberToSpecResidueField z ≫
              (Spec.map (CommRingCat.ofHom (Scheme.Hom.ResidueField.mapOfSpec A.hom z)) ≫
                η[A].left) := by
              exact
                congrArg
                  (fun g : Spec (CommRingCat.of (A.left.residueField z)) ⟶ A.left ↦
                    (m₃.left).fiberToSpecResidueField z ≫ g)
                  hFromSpecUnit
        _ = sfToBase ≫ η[A].left := by
              rfl
    have hm₁₂₃ : s₃ ≫ m₁₂₃ = s₃ ≫ m₁₂ := by
      -- Multiplication by the unit collapses the third factor on the fibre face.
      calc
        s₃ ≫ m₁₂₃ = (s₃ ≫ m₁₂) * (s₃ ≫ m₃) := by
          rw [MonObj.comp_mul]
        _ = s₃ ≫ m₁₂ := by
          rw [hm₃_one]
          simp
    have hm₁₃ : s₃ ≫ m₁₃ = s₃ ≫ m₁ := by
      -- The same unit reduction collapses `m₁₃` to the first projection.
      calc
        s₃ ≫ m₁₃ = (s₃ ≫ m₁) * (s₃ ≫ m₃) := by
          rw [MonObj.comp_mul]
        _ = s₃ ≫ m₁ := by
          rw [hm₃_one]
          simp
    have hm₂₃ : s₃ ≫ m₂₃ = s₃ ≫ m₂ := by
      -- The same unit reduction collapses `m₂₃` to the second projection.
      calc
        s₃ ≫ m₂₃ = (s₃ ≫ m₂) * (s₃ ≫ m₃) := by
          rw [MonObj.comp_mul]
        _ = s₃ ≫ m₂ := by
          rw [hm₃_one]
          simp
    let R₁₂ := (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁₂)
    let R₁₃ := (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁₃)
    let R₂₃ := (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₂₃)
    let C₃ := (Scheme.Modules.pullback S₃.hom).obj ((Scheme.Modules.pullback η[A].left).obj L)
    have e₁₂₃ :
        (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁₂₃) ≅ R₁₂ := by
      exact pullbackPullbackIsoOfCompEq s₃.left m₁₂₃.left m₁₂.left L
        (congrArg Over.Hom.left hm₁₂₃)
    have e₁ :
        (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁) ≅ R₁₃ := by
      exact pullbackPullbackIsoOfCompEq s₃.left m₁.left m₁₃.left L
        (congrArg Over.Hom.left hm₁₃).symm
    have e₂ :
        (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₂) ≅ R₂₃ := by
      exact pullbackPullbackIsoOfCompEq s₃.left m₂.left m₂₃.left L
        (congrArg Over.Hom.left hm₂₃).symm
    have e₃ :
        (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₃) ≅ C₃ := by
      have hm₃_left : s₃.left ≫ m₃.left = S₃.hom ≫ η[A].left := by
        simpa [Hom.one_def] using congrArg Over.Hom.left hm₃_one
      exact
        (Scheme.Modules.pullbackComp s₃.left m₃.left).app L ≪≫
          (Scheme.Modules.pullbackCongr hm₃_left).app L ≪≫
            ((Scheme.Modules.pullbackComp S₃.hom η[A].left).app L).symm
    have hInvEta :
        Scheme.Modules.Invertible ((Scheme.Modules.pullback (Over.Hom.left η[A])).obj L) := by
      simpa using (Scheme.Modules.pullback_isInvertible (f := η[A].left) L)
    have hC₃ : RingedSpace.IsTrivial C₃ := by
      -- Pulling back the base-point module along the fibre source stays trivial.
      exact
        @pullbackBasePointModuleIsTrivial
          _ _ _ S₃.hom ((Scheme.Modules.pullback η[A].left).obj L) hInvEta
    have rhsFactor :
        (Scheme.Modules.pullback s₃.left).obj rhs ≅ R₁₂ ⊗ (R₁₃ ⊗ R₂₃) := by
      -- Expand the restricted right-hand tensor into its three factor pullbacks.
      calc
        (Scheme.Modules.pullback s₃.left).obj rhs
            ≅
              (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁₂) ⊗
                (Scheme.Modules.pullback s₃.left).obj
                  (pullbackModule m₁₃ ⊗ pullbackModule m₂₃) := by
              simpa [rhs] using
                (Scheme.Modules.pullbackTensorIso s₃.left
                  (pullbackModule m₁₂)
                  (pullbackModule m₁₃ ⊗ pullbackModule m₂₃))
        _ ≅ R₁₂ ⊗
              ((Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁₃) ⊗
                (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₂₃)) := by
              simpa [R₁₂] using
                (Iso.refl ((Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁₂)) ⊗ᵢ
                  (Scheme.Modules.pullbackTensorIso s₃.left
                    (pullbackModule m₁₃) (pullbackModule m₂₃)))
        _ ≅ R₁₂ ⊗ (R₁₃ ⊗ R₂₃) := by
              simpa [R₁₃, R₂₃] using
                (Iso.refl
                  (R₁₂ ⊗
                    ((Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁₃) ⊗
                      (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₂₃))))
    have lhsFactor :
        (Scheme.Modules.pullback s₃.left).obj lhs ≅ R₁₂ ⊗ (R₁₃ ⊗ (R₂₃ ⊗ C₃)) := by
      -- Expand the restricted left-hand tensor and rewrite each factor using the fibre-face data.
      calc
        (Scheme.Modules.pullback s₃.left).obj lhs
            ≅
              (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁₂₃) ⊗
                (Scheme.Modules.pullback s₃.left).obj
                  (pullbackModule m₁ ⊗
                    (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [lhs] using
                (Scheme.Modules.pullbackTensorIso s₃.left
                  (pullbackModule m₁₂₃)
                  (pullbackModule m₁ ⊗
                    (pullbackModule m₂ ⊗ pullbackModule m₃)))
        _ ≅ R₁₂ ⊗
              (Scheme.Modules.pullback s₃.left).obj
                (pullbackModule m₁ ⊗
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [R₁₂] using
                (e₁₂₃ ⊗ᵢ
                  Iso.refl
                    ((Scheme.Modules.pullback s₃.left).obj
                      (pullbackModule m₁ ⊗
                        (pullbackModule m₂ ⊗ pullbackModule m₃))))
        _ ≅ R₁₂ ⊗
              ((Scheme.Modules.pullback s₃.left).obj (pullbackModule m₁) ⊗
                (Scheme.Modules.pullback s₃.left).obj
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa using
                (Iso.refl R₁₂ ⊗ᵢ
                  (Scheme.Modules.pullbackTensorIso s₃.left
                    (pullbackModule m₁)
                    (pullbackModule m₂ ⊗ pullbackModule m₃)))
        _ ≅ R₁₂ ⊗
              (R₁₃ ⊗
                (Scheme.Modules.pullback s₃.left).obj
                  (pullbackModule m₂ ⊗ pullbackModule m₃)) := by
              simpa [R₁₃] using
                (Iso.refl R₁₂ ⊗ᵢ
                  (e₁ ⊗ᵢ
                    Iso.refl
                      ((Scheme.Modules.pullback s₃.left).obj
                        (pullbackModule m₂ ⊗ pullbackModule m₃))))
        _ ≅ R₁₂ ⊗
              (R₁₃ ⊗
                ((Scheme.Modules.pullback s₃.left).obj (pullbackModule m₂) ⊗
                  (Scheme.Modules.pullback s₃.left).obj (pullbackModule m₃))) := by
              simpa [Category.assoc] using
                (Iso.refl R₁₂ ⊗ᵢ
                  (Iso.refl R₁₃ ⊗ᵢ
                    (Scheme.Modules.pullbackTensorIso s₃.left
                      (pullbackModule m₂) (pullbackModule m₃))))
        _ ≅ R₁₂ ⊗ (R₁₃ ⊗ (R₂₃ ⊗ C₃)) := by
              simpa [R₂₃, C₃] using
                (Iso.refl R₁₂ ⊗ᵢ (Iso.refl R₁₃ ⊗ᵢ (e₂ ⊗ᵢ e₃)))
    have tensorAssembly :
        R₁₂ ⊗ (R₁₃ ⊗ (R₂₃ ⊗ C₃)) ≅ C₃ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := by
      -- Move the trivial factor from the far right to the front.
      calc
        R₁₂ ⊗ (R₁₃ ⊗ (R₂₃ ⊗ C₃))
            ≅ (R₁₂ ⊗ R₁₃) ⊗ (R₂₃ ⊗ C₃) := (α_ R₁₂ R₁₃ (R₂₃ ⊗ C₃)).symm
        _ ≅ (R₁₂ ⊗ R₁₃) ⊗ (C₃ ⊗ R₂₃) := Iso.refl _ ⊗ᵢ (β_ R₂₃ C₃)
        _ ≅ R₁₂ ⊗ (R₁₃ ⊗ (C₃ ⊗ R₂₃)) := α_ R₁₂ R₁₃ (C₃ ⊗ R₂₃)
        _ ≅ R₁₂ ⊗ ((R₁₃ ⊗ C₃) ⊗ R₂₃) := Iso.refl _ ⊗ᵢ (α_ R₁₃ C₃ R₂₃).symm
        _ ≅ R₁₂ ⊗ ((C₃ ⊗ R₁₃) ⊗ R₂₃) := Iso.refl _ ⊗ᵢ ((β_ R₁₃ C₃) ⊗ᵢ Iso.refl _)
        _ ≅ R₁₂ ⊗ (C₃ ⊗ (R₁₃ ⊗ R₂₃)) := Iso.refl _ ⊗ᵢ (α_ C₃ R₁₃ R₂₃)
        _ ≅ (R₁₂ ⊗ C₃) ⊗ (R₁₃ ⊗ R₂₃) := (α_ R₁₂ C₃ (R₁₃ ⊗ R₂₃)).symm
        _ ≅ (C₃ ⊗ R₁₂) ⊗ (R₁₃ ⊗ R₂₃) := (β_ R₁₂ C₃) ⊗ᵢ Iso.refl _
        _ ≅ C₃ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := α_ C₃ R₁₂ (R₁₃ ⊗ R₂₃)
    have factorization :
        (Scheme.Modules.pullback s₃.left).obj lhs ≅
          C₃ ⊗ (Scheme.Modules.pullback s₃.left).obj rhs := by
      -- Assemble the transported fibre factors and fold the restricted right-hand tensor back.
      calc
        (Scheme.Modules.pullback s₃.left).obj lhs
            ≅ R₁₂ ⊗ (R₁₃ ⊗ (R₂₃ ⊗ C₃)) := lhsFactor
        _ ≅ C₃ ⊗ (R₁₂ ⊗ (R₁₃ ⊗ R₂₃)) := tensorAssembly
        _ ≅ C₃ ⊗ (Scheme.Modules.pullback s₃.left).obj rhs := by
              exact (tensorLeft C₃).mapIso rhsFactor.symm
    -- The generic factorization-to-triviality lemma now closes the fibre face.
    exact cubeRestrictionIsTrivialOfFactorization s₃.left factorization hC₃
  have hcube : RingedSpace.IsTrivial (lhs ⊗ ((ihom rhs).obj (𝟙_ T.left.Modules))) :=
    @Scheme.Modules.Invertible.isTrivial_of_cube
      _ _ _ _ A.hom A.hom A.hom
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
      σ σ z (lhs ⊗ ((ihom rhs).obj (𝟙_ T.left.Modules))) hInvCube
      h_first h_second h_fibre
  change Nonempty (lhs ≅ rhs)
  rcases hcube with ⟨e⟩
  let e' : ((ihom rhs).obj (𝟙_ T.left.Modules)) ⊗ lhs ≅ 𝟙_ T.left.Modules :=
    (β_ ((ihom rhs).obj (𝟙_ T.left.Modules)) lhs) ≪≫ e
  let i : lhs ≅ ((ihom ((ihom rhs).obj (𝟙_ T.left.Modules))).obj (𝟙_ T.left.Modules)) :=
    MonoidalClosed.RightInverse.isoIhomUnit
      ((ihom rhs).obj (𝟙_ T.left.Modules)) lhs e'
  let j₁ : MonoidalCategory.isInvertibleObject.inverse rhs ≅
      ((ihom rhs).obj (𝟙_ T.left.Modules)) :=
    MonoidalClosed.RightInverse.isoIhomUnit rhs
      (MonoidalCategory.isInvertibleObject.inverse rhs)
      (MonoidalCategory.isInvertibleObject.tensorInverseIso rhs)
  let e'' : ((ihom rhs).obj (𝟙_ T.left.Modules)) ⊗ rhs ≅ 𝟙_ T.left.Modules :=
    (j₁.symm ⊗ᵢ Iso.refl rhs) ≪≫ MonoidalCategory.isInvertibleObject.inverseTensorIso rhs
  let j : ((ihom ((ihom rhs).obj (𝟙_ T.left.Modules))).obj (𝟙_ T.left.Modules)) ≅ rhs :=
    (MonoidalClosed.RightInverse.isoIhomUnit
      ((ihom rhs).obj (𝟙_ T.left.Modules)) rhs e'').symm
  exact ⟨i ≪≫ j⟩

end AlgebraicGeometry.AbelianVariety
