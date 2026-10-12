/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Coordinate
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingLocus
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections

/-!
# Tautological vanishing loci of linear systems

A family of global sections of an invertible module on a scheme `X` over a field
determines a tautological section of `p^*𝒪(1) ⊗ q^*L` on `ℙ^n ×_k X`, and hence a
canonical closed subscheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LinearSystem

variable {k : Type u} [Field k]

/-- The fibre product `ℙ^n ×_k X`. -/
abbrev product (X : SchemeOverField k) (n : ℕ) : Scheme :=
  pullback (ProjectiveSpace.toSpec k n) X.hom

/-- The projection `ℙ^n ×_k X ⟶ ℙ^n`. -/
abbrev fst (X : SchemeOverField k) (n : ℕ) :
    product X n ⟶ ProjectiveSpace.scheme k n :=
  pullback.fst (ProjectiveSpace.toSpec k n) X.hom

/-- The projection `ℙ^n ×_k X ⟶ X`. -/
abbrev snd (X : SchemeOverField k) (n : ℕ) :
    product X n ⟶ X.left :=
  pullback.snd (ProjectiveSpace.toSpec k n) X.hom

/-- The external tensor product `p^*𝒪(1) ⊗ q^*L` on `ℙ^n ×_k X`. -/
abbrev tautologicalModule (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ) :
    (product X n).Modules :=
  Scheme.Modules.externalTensorProduct
    (ProjectiveSpace.toSpec k n) X.hom (ProjectiveSpace.twistingSheaf k n 1) L

/-- The tautological module `p^*𝒪(1) ⊗ q^*L` is invertible. -/
theorem tautologicalModule_isInvertible
    (X : SchemeOverField k) (L : X.left.Modules) [Scheme.Modules.Invertible L] (n : ℕ) :
    Scheme.Modules.Invertible (tautologicalModule X L n) :=
  sorry

/-- The pullback to `ℙ^n ×_k X` of the homogeneous coordinate section `T_i`. -/
noncomputable abbrev pullbackCoordinateSection
    (X : SchemeOverField k) (n : ℕ) (i : Fin (n + 1)) :
    ((Scheme.Modules.pullback (fst X n)).obj (ProjectiveSpace.twistingSheaf k n 1)).sections :=
  Scheme.Modules.sectionsPullback (fst X n) (ProjectiveSpace.twistingSheaf k n 1)
    (ProjectiveSpace.coordinateTwistSection k n i)

/-- The pullback to `ℙ^n ×_k X` of a global section of `L`. -/
noncomputable abbrev pullbackLinearSection
    (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ)
    (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) (i : Fin (n + 1)) :
    ((Scheme.Modules.pullback (snd X n)).obj L).sections :=
  Scheme.Modules.sectionsPullback (snd X n) L (RingedSpace.sectionFromTop L (s i))

/-- The top-open value of the pullback of `T_i`. -/
noncomputable abbrev pullbackCoordinate
    (X : SchemeOverField k) (n : ℕ) (i : Fin (n + 1)) :
    Γ(((Scheme.Modules.pullback (fst X n)).obj (ProjectiveSpace.twistingSheaf k n 1)), ⊤) :=
  (pullbackCoordinateSection X n i).1 (op (⊤ : (product X n).Opens))

/-- The top-open value of the pullback of `s i`. -/
noncomputable abbrev pullbackLinear
    (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ)
    (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) (i : Fin (n + 1)) :
    Γ(((Scheme.Modules.pullback (snd X n)).obj L), ⊤) :=
  (pullbackLinearSection X L n s i).1 (op (⊤ : (product X n).Opens))

/-- The top-open value of the pure tensor `T_i ⊗ s i` on `ℙ^n ×_k X`. -/
noncomputable def tautologicalPureTensor
    (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ)
    (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) (i : Fin (n + 1)) :
    Γ(tautologicalModule X L n, ⊤) :=
  SheafOfModules.RingedSite.tensorSection (product X n).sheaf
    (op (⊤ : (product X n).Opens))
    (pullbackCoordinate X n i) (pullbackLinear X L n s i)

/-- The tautological section `∑ i, T_i ⊗ s i` of `p^*𝒪(1) ⊗ q^*L`. -/
noncomputable def tautologicalSection
    (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ)
    (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) :
    (tautologicalModule X L n).sections :=
  RingedSpace.sectionFromTop (tautologicalModule X L n)
    (∑ i, tautologicalPureTensor X L n s i)

/-- The tautological section is the indicated finite sum of pure tensors. -/
theorem tautologicalSection_eq_sum
    (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ)
    (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) :
    tautologicalSection X L n s =
      RingedSpace.sectionFromTop (tautologicalModule X L n)
        (∑ i, tautologicalPureTensor X L n s i) :=
  sorry

/-- The closed subscheme of `ℙ^n ×_k X` cut out by `∑ i, T_i ⊗ s i`. -/
noncomputable def vanishingIdeal
    (X : SchemeOverField k) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) :
    (product X n).IdealSheafData :=
  @Scheme.zeroIdealSheaf (product X n) _
    (tautologicalModule X L n)
    (Scheme.Modules.Invertible.tensorRight_isEquivalence
      (tautologicalModule_isInvertible X L n))
    (tautologicalSection X L n s)

/-- The vanishing ideal is the zero ideal sheaf of the tautological section. -/
theorem vanishingIdeal_eq_zeroIdealSheaf
    (X : SchemeOverField k) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) :
    vanishingIdeal X L n s =
      @Scheme.zeroIdealSheaf (product X n) _
        (tautologicalModule X L n)
        (Scheme.Modules.Invertible.tensorRight_isEquivalence
          (tautologicalModule_isInvertible X L n))
        (tautologicalSection X L n s) :=
  sorry

/-- The closed subscheme underlying `vanishingIdeal`. -/
noncomputable abbrev vanishingLocus
    (X : SchemeOverField k) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) : Scheme :=
  (vanishingIdeal X L n s).subscheme

/-- The closed immersion of `vanishingLocus` into `ℙ^n ×_k X`. -/
noncomputable abbrev vanishingLocusι
    (X : SchemeOverField k) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) :
    vanishingLocus X L n s ⟶ product X n :=
  (vanishingIdeal X L n s).subschemeι

/-- The global section `∑ i, v i • s i` of `L`. -/
noncomputable def linearCombination
    (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ)
    (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    (v : Fin (n + 1) → k) : L.sections :=
  RingedSpace.sectionFromTop L (∑ i, v i • s i)

/-- The linear combination is the indicated finite sum of scalar multiples. -/
theorem linearCombination_eq_sum
    (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ)
    (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    (v : Fin (n + 1) → k) :
    linearCombination X L n s v = RingedSpace.sectionFromTop L (∑ i, v i • s i) :=
  sorry

/-- Vanishing of a linear combination of sections is invariant under scaling the
coefficients by a unit of `k`. -/
theorem mem_sectionNonvanishingLocus_linearCombination_units_iff
    (X : SchemeOverField k) (L : X.left.Modules) (n : ℕ)
    (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    (v : Fin (n + 1) → k) (t : kˣ) {x : X.left} :
    x ∈ RingedSpace.sectionNonvanishingLocus X.left.toRingedSpace L
        (linearCombination X L n s v) ↔
      x ∈ RingedSpace.sectionNonvanishingLocus X.left.toRingedSpace L
        (linearCombination X L n s fun i ↦ (t : k) * v i) :=
  sorry

end AlgebraicGeometry.LinearSystem
