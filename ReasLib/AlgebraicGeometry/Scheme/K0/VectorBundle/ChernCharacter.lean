module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Ring
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.ExactSequence
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter.Tensor
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Rational

/-!
# The Chern character on vector-bundle K-theory

The componentwise Chern character descends through short-exact relations and is
bundled here as a ring homomorphism from vector-bundle `K₀`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The completed Chern-character value of a finite locally free module. -/
noncomputable def chernCharacterValue (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    ChowCohomology.Nonnegative.RationalCompletion δ p :=
  fun i ↦ @ChernClass.Theory.characterComponent _ _ δ p _ _ _
    classes E.obj E.property i

/-- The coefficient of the completed generator value is the corresponding
Chern-character component. -/
theorem chernCharacterValue_apply (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℕ) :
    chernCharacterValue δ p classes E i =
      @ChernClass.Theory.characterComponent _ _ δ p _ _ _
        classes E.obj E.property i := sorry

/-- Completed Chern-character values are additive on short exact sequences of
finite locally free modules. -/
theorem chernCharacterValue_shortExact (classes : ChernClass.Theory δ p)
    (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (hC : C.ShortExact) :
    (fun i ↦ ChernClass.Theory.characterComponent δ p classes C.X₂ i) =
      (fun i ↦ ChernClass.Theory.characterComponent δ p classes C.X₁ i) +
        fun i ↦ ChernClass.Theory.characterComponent δ p classes C.X₃ i := sorry

/-- Completed Chern-character values send the structure module to the convolution unit. -/
theorem chernCharacterValue_unit (classes : ChernClass.Theory δ p) :
    chernCharacterValue δ p classes (unitObject X) = 1 := sorry

/-- Completed Chern-character values send tensor products to convolution products. -/
theorem chernCharacterValue_tensor (classes : ChernClass.Theory δ p)
    (E F : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    chernCharacterValue δ p classes (tensorObj X E F) =
      chernCharacterValue δ p classes E * chernCharacterValue δ p classes F := sorry

/-- Short-exact relations lie in the kernel of the free additive lift of the
completed Chern-character value. -/
theorem relations_le_ker_chernCharacter (classes : ChernClass.Theory δ p) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ≤
      (FreeAbelianGroup.lift (chernCharacterValue δ p classes)).ker := sorry

/-- The additive Chern character obtained by descent to vector-bundle `K₀`. -/
noncomputable def chernCharacterAdd (classes : ChernClass.Theory δ p) :
    VectorBundleK0 X →+ ChowCohomology.Nonnegative.RationalCompletion δ p :=
  ObjectProperty.GrothendieckGroup.lift (chernCharacterValue δ p classes)
    (relations_le_ker_chernCharacter δ p classes)

/-- The additive Chern character has the prescribed value on a vector-bundle generator. -/
theorem chernCharacterAdd_of (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    chernCharacterAdd δ p classes
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      chernCharacterValue δ p classes E := sorry

/-- The additive Chern character preserves the vector-bundle unit class. -/
theorem chernCharacterAdd_map_one (classes : ChernClass.Theory δ p) :
    chernCharacterAdd δ p classes (1 : VectorBundleK0 X) = 1 := sorry

/-- The additive Chern character preserves tensor-induced multiplication. -/
theorem chernCharacterAdd_map_mul (classes : ChernClass.Theory δ p)
    (a b : VectorBundleK0 X) :
    chernCharacterAdd δ p classes (a * b) =
      chernCharacterAdd δ p classes a * chernCharacterAdd δ p classes b := sorry

/-- The Chern character from vector-bundle `K₀` to completed rational Chow cohomology. -/
noncomputable def chernCharacter (classes : ChernClass.Theory δ p) :
    VectorBundleK0 X →+* ChowCohomology.Nonnegative.RationalCompletion δ p :=
  { chernCharacterAdd δ p classes with
    map_one' := chernCharacterAdd_map_one δ p classes
    map_mul' := chernCharacterAdd_map_mul δ p classes }

/-- The additive part of the Chern-character ring homomorphism is `chernCharacterAdd`. -/
theorem chernCharacter_toAddMonoidHom (classes : ChernClass.Theory δ p) :
    (chernCharacter δ p classes).toAddMonoidHom = chernCharacterAdd δ p classes := sorry

/-- The Chern character sends a vector-bundle generator to its componentwise character. -/
theorem chernCharacter_of (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    chernCharacter δ p classes
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      chernCharacterValue δ p classes E := sorry

/-- A ring homomorphism out of vector-bundle `K₀` is the Chern character when it has
the prescribed value on every vector-bundle generator. -/
theorem chernCharacter_eq_of_eq_on_generators (classes : ChernClass.Theory δ p)
    (f : VectorBundleK0 X →+* ChowCohomology.Nonnegative.RationalCompletion δ p)
    (h : ∀ E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules),
      f (ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
          chernCharacterValue δ p classes E) :
    f = chernCharacter δ p classes := sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
