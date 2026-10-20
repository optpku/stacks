module

public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition

@[expose] public section

noncomputable section

open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C]
variable (G : A ⥤ B) [G.Additive] [G.PreservesHomology]
variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]

set_option backward.isDefEq.respectTransparency false in
/-- The exact image of an injective resolution maps to an injective resolution of the
image object, by extending its augmentation recursively into the injective target terms. -/
def precompExactResolutionMap (X : A) :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex ⟶
      (injectiveResolution (G.obj X)).cocomplex := by
  let source := injectiveResolution X
  let target := injectiveResolution (G.obj X)
  let image := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj source.cocomplex
  have mapped_mono : Mono (G.map (source.ι.f 0)) := by
    have preservation := Functor.PreservesHomology.preservesKernel G (source.cocomplex.d 0 1)
    exact mono_of_isLimit_fork (KernelFork.mapIsLimit _ source.isLimitKernelFork G)
  let first : image.X 0 ⟶ target.cocomplex.X 0 :=
    @Injective.factorThru B _ (target.cocomplex.X 0) (G.obj X) (image.X 0)
      inferInstance (target.ι.f 0) (G.map (source.ι.f 0)) mapped_mono
  have first_cycle : G.map (source.ι.f 0) ≫ (first ≫ target.cocomplex.d 0 1) = 0 := by
    dsimp [first]
    rw [← Category.assoc, @Injective.comp_factorThru B _ _ _ _ _ _ _ mapped_mono]
    exact target.ι_f_zero_comp_complex_d
  let second : image.X 1 ⟶ target.cocomplex.X 1 :=
    (source.exact₀.map G).descToInjective (first ≫ target.cocomplex.d 0 1) first_cycle
  have comm : first ≫ target.cocomplex.d 0 1 = image.d 0 1 ≫ second :=
    ((source.exact₀.map G).comp_descToInjective _ _).symm
  refine CochainComplex.mkHom image target.cocomplex first second comm ?_
  intro degree ⟨previous, current, square⟩
  have cycle : G.map (source.cocomplex.d degree (degree + 1)) ≫
      (current ≫ target.cocomplex.d (degree + 1) (degree + 2)) = 0 := by
    change image.d degree (degree + 1) ≫
      (current ≫ target.cocomplex.d (degree + 1) (degree + 2)) = 0
    rw [← Category.assoc, ← square, Category.assoc]
    simp
  exact ⟨(source.exact_succ degree |>.map G).descToInjective
      (current ≫ target.cocomplex.d (degree + 1) (degree + 2)) cycle,
    ((source.exact_succ degree |>.map G).comp_descToInjective _ _).symm⟩

/-- The exact-precomposition resolution comparison extends the mapped augmentation. -/
@[reassoc]
theorem precompExactResolutionMap_comm (X : A) :
    G.map ((injectiveResolution X).ι.f 0) ≫ (precompExactResolutionMap G X).f 0 =
      (injectiveResolution (G.obj X)).ι.f 0 := sorry

/-- Exact precomposition induces a forward map from the derived composite to the
derived functor evaluated on the image object, without preserving injective objects. -/
def precompExactComparisonApp (F : B ⥤ C) [F.Additive] (degree : ℕ) (X : A) :
    ((G ⋙ F).rightDerived degree).obj X ⟶ (G ⋙ F.rightDerived degree).obj X :=
  ((injectiveResolution X).isoRightDerivedObj (G ⋙ F) degree).hom ≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) degree).map
      (((mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) (ComplexShape.up ℕ)).symm.app
          (injectiveResolution X).cocomplex).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (precompExactResolutionMap G X)) ≫
    ((injectiveResolution (G.obj X)).isoRightDerivedObj F degree).inv

/-- The forward comparison for exact precomposition is natural in the source object. -/
@[reassoc]
theorem precompExactComparison_naturality (F : B ⥤ C) [F.Additive]
    (degree : ℕ) {X Y : A} (morphism : X ⟶ Y) :
    ((G ⋙ F).rightDerived degree).map morphism ≫
        precompExactComparisonApp G F degree Y =
      precompExactComparisonApp G F degree X ≫ (G ⋙ F.rightDerived degree).map morphism :=
  sorry

/-- The natural forward comparison from deriving an exact precomposition to
precomposing the derived functor. -/
def precompExactComparison (F : B ⥤ C) [F.Additive] (degree : ℕ) :
    (G ⋙ F).rightDerived degree ⟶ G ⋙ F.rightDerived degree where
  app := precompExactComparisonApp G F degree
  naturality _ _ morphism := precompExactComparison_naturality G F degree morphism

end CategoryTheory.Functor.RightDerived
