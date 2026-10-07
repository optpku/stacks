module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Data.Fintype.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.FinitePartDecomposition

@[expose] public section

/-!
# Finite and finite-type algebras over henselian local rings

@stack 04GJ

This leaf owns the concrete product presentation of a finite algebra over a
henselian local ring by henselian local finite factors, and the corresponding
finite-type split with a residual non-quasi-finite part. The index and residual
source algebra remain in the source universe, while factors use the ambient
universe needed for the base algebra. It also records the local-target
consequences of that presentation at the product, ring-map, and canonical
algebra-map levels.
-/

universe u v

namespace HenselianLocalRing

open IsLocalRing

/-- A finite algebra presented as a finite product of henselian local algebras
which are module-finite over the base. -/
@[stacks 04GH "finite henselian local algebra decomposition"]
structure FiniteProduct (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] where
  /-- The finite index type of local factors. -/
  index : Type v
  /-- The finiteness structure on the index type. -/
  [fintype : Fintype index]
  /-- The henselian local factor at each index. -/
  factor : index → Type (max u v)
  /-- The commutative-ring structure on each factor. -/
  [factorCommRing : ∀ i, CommRing (factor i)]
  /-- The `R`-algebra structure on each factor. -/
  [factorAlgebra : ∀ i, Algebra R (factor i)]
  /-- Each factor is henselian local. -/
  [factorHenselian : ∀ i, HenselianLocalRing (factor i)]
  /-- Each factor is module-finite over `R`. -/
  [factorModuleFinite : ∀ i, Module.Finite R (factor i)]
  /-- The algebra equivalence giving the finite product presentation. -/
  equiv : S ≃ₐ[R] ∀ i, factor i

namespace FiniteProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Build a finite henselian-local decomposition from concrete factors and an
algebra equivalence to their product. -/
@[stacks 04GH "finite henselian local algebra decomposition constructor"]
def of {ι : Type v} [Fintype ι] (A : ι → Type (max u v))
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, HenselianLocalRing (A i)] [∀ i, Module.Finite R (A i)]
    (equiv : S ≃ₐ[R] ∀ i, A i) : FiniteProduct R S where
  index := ι
  fintype := inferInstance
  factor := A
  factorCommRing := inferInstance
  factorAlgebra := inferInstance
  factorHenselian := inferInstance
  factorModuleFinite := inferInstance
  equiv := equiv

/-- Each factor in a finite henselian-local product presentation defines a
finite commutative algebra over the base ring. -/
def factorObj (D : FiniteProduct R S) (i : D.index) : CommAlgCat.Finite.{max u v} R :=
  @CommAlgCat.Finite.of R _ (D.factor i) (D.factorCommRing i)
    (D.factorAlgebra i) (D.factorModuleFinite i)

/-- A finite henselian-local product presentation has finitely many factors,
each henselian local and module-finite over the base ring. -/
theorem spec (D : FiniteProduct R S) :
    Finite D.index ∧ ∀ i : D.index,
      HenselianLocalRing (D.factorObj i) ∧ Module.Finite R (D.factorObj i) := sorry

/-- A finite algebra over a henselian local ring has a finite product
presentation by henselian local algebras that are finite over the base. -/
@[stacks 04GH "finite henselian local algebra decomposition exists"]
theorem nonempty
    [HenselianLocalRing R] [Module.Finite R S] :
    Nonempty (FiniteProduct R S) := sorry

/-- A local algebra with a finite henselian-local product presentation is
henselian local. -/
@[stacks 04GH "local factor of finite henselian product"]
theorem henselian (D : FiniteProduct R S) [IsLocalRing S] :
    HenselianLocalRing S := sorry

end FiniteProduct

/-- A local target of a finite map from a henselian local ring is henselian
local.  The map is explicit so this applies to arbitrary finite ring maps,
not only to a preselected algebra structure. -/
@[stacks 04GH "finite local algebra over henselian local ring"]
theorem of_finite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [IsLocalRing S] (f : R →+* S) (hf : f.Finite) :
    HenselianLocalRing S := sorry

/-- A module-finite local algebra over a henselian local ring is henselian
local.  This is the direct algebra-map interface for downstream use. -/
@[stacks 04GH "finite local algebra over henselian local ring"]
theorem of_moduleFinite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [IsLocalRing S] [Module.Finite R S] :
    HenselianLocalRing S := sorry

namespace FiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A finite-type algebra over a henselian local ring has a finite
part presented as a finite product of henselian local finite algebras, with a
remainder having no quasi-finite point over the closed point. -/
@[stacks 04GJ "henselian finite-type decomposition"]
theorem existsFinitePartDecomposition
    [HenselianLocalRing R] [Algebra.FiniteType R S] :
    ∃ D : Algebra.FinitePartDecomposition R S,
      ∃ E : FiniteProduct R D.finitePart,
        D.noQuasiFinitePoints (closedPoint R) := sorry

end FiniteType

end HenselianLocalRing
