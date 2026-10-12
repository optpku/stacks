/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernCharacter
public import ReasLib.CategoryTheory.Pretriangulated.K0.Universal
public import stacks_project.Chap42.Remark_42_56_12_ChernClass
public import stacks_project.Chap42.Lemma_42_46_11

/-!
# The Chern character on perfect `K₀`

Under the same size hypothesis as the total Chern class, derived Chern characters
of Definition 42.46.3 lift additively through triangle relations and
multiplicatively through derived tensor product to a ring homomorphism
`K0 X →+* RationalCompletion δ p`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The completed Chern-character value of a perfect complex. -/
def chernCharacterValue
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    ChowCohomology.Nonnegative.RationalCompletion δ p :=
  ChernClass.Derived.character δ p classes E.obj E.property (isDefined_of_hqc δ p hqc E)

/-- The coefficient of the completed generator value is the corresponding
derived Chern-character component. -/
theorem chernCharacterValue_apply
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) (i : ℕ) :
    chernCharacterValue δ p hqc classes E i =
      ChernClass.Derived.character δ p classes E.obj E.property
        (isDefined_of_hqc δ p hqc E) i := sorry

/-- Completed Chern-character values are additive on distinguished triangles of
perfect complexes. -/
theorem chernCharacterValue_distinguished
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (T : Triangle (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))) :
    chernCharacterValue δ p hqc classes T.obj₂ =
      chernCharacterValue δ p hqc classes T.obj₁ +
        chernCharacterValue δ p hqc classes T.obj₃ := sorry

/-- Completed Chern-character values send the structure sheaf in degree zero to the
convolution unit. -/
theorem chernCharacterValue_unit
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) :
    chernCharacterValue δ p hqc classes (unitObject X) = 1 := sorry

/-- Completed Chern-character values send derived tensor products to convolution products. -/
theorem chernCharacterValue_tensor
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E F : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    chernCharacterValue δ p hqc classes (tensorObj X E F) =
      chernCharacterValue δ p hqc classes E * chernCharacterValue δ p hqc classes F :=
  sorry

/-- The additive Chern character obtained by descent to perfect `K₀`. -/
def chernCharacterAdd
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) :
    K0 X →+ ChowCohomology.Nonnegative.RationalCompletion δ p :=
  TriangulatedK0.liftOfDistinguished (chernCharacterValue δ p hqc classes)
    (chernCharacterValue_distinguished δ p hqc classes)

/-- The additive Chern character has the prescribed value on a perfect-complex generator. -/
theorem chernCharacterAdd_of
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    chernCharacterAdd δ p hqc classes (TriangulatedK0.of E) =
      chernCharacterValue δ p hqc classes E := sorry

/-- The additive Chern character preserves the structure-sheaf unit class. -/
theorem chernCharacterAdd_map_one
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) :
    chernCharacterAdd δ p hqc classes (1 : K0 X) = 1 := sorry

/-- The additive Chern character preserves derived-tensor multiplication. -/
theorem chernCharacterAdd_map_mul
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) (a b : K0 X) :
    chernCharacterAdd δ p hqc classes (a * b) =
      chernCharacterAdd δ p hqc classes a * chernCharacterAdd δ p hqc classes b :=
  sorry

/-- The Chern character from perfect `K₀` to completed rational Chow cohomology. -/
def chernCharacter
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) :
    K0 X →+* ChowCohomology.Nonnegative.RationalCompletion δ p :=
  { chernCharacterAdd δ p hqc classes with
    map_one' := chernCharacterAdd_map_one δ p hqc classes
    map_mul' := chernCharacterAdd_map_mul δ p hqc classes }

/-- The additive part of the Chern-character ring homomorphism is `chernCharacterAdd`. -/
theorem chernCharacter_toAddMonoidHom
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) :
    (chernCharacter δ p hqc classes).toAddMonoidHom =
      chernCharacterAdd δ p hqc classes := sorry

/-- The Chern character sends a perfect-complex generator to its componentwise character. -/
theorem chernCharacter_of
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    chernCharacter δ p hqc classes (TriangulatedK0.of E) =
      chernCharacterValue δ p hqc classes E := sorry

/-- The Chern character of a finite locally free module, placed in degree zero, recovers
the vector-bundle Chern character. -/
theorem chernCharacter_comp_toK0
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) (a : VectorBundleK0 X) :
    chernCharacter δ p hqc classes (VectorBundleK0.toK0 X a) =
      VectorBundleK0.chernCharacter δ p classes a := sorry

end AlgebraicGeometry.Scheme.K0
