module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Surjectivity loci of module morphisms

The complement of the image of the cokernel support represents surjectivity after
base change when the target module is finite type with support proper over the base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)

/-- The set of points of the base complementary to the image of the cokernel support. -/
def surjectivityLocus : Set (Points B) :=
  (Points.map f '' moduleSupport (cokernel u))ᶜ

/-- The surjectivity locus is the complement of the image of the cokernel support. -/
theorem surjectivityLocus_eq :
    surjectivityLocus f u = (Points.map f '' moduleSupport (cokernel u))ᶜ :=
  rfl

/-- The complement of the image of the cokernel support is open when the target module
is of finite type and its scheme-theoretic support is proper over the base. -/
theorem isOpen_surjectivityLocus [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    IsOpen (surjectivityLocus f u) :=
  sorry

/-- The open set complementary to the image of the cokernel support. -/
def surjectivityOpens [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    Opens (Points B) :=
  Opens.mk (surjectivityLocus f u) (isOpen_surjectivityLocus f u)

/-- The open subspace cut out by the complement of the image of the cokernel support. -/
def surjectivityOpenSubspace [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    OpenSubspace B :=
  OpenSubspace.fromOpens (surjectivityOpens f u)

/-- The point set of the surjectivity open subspace is the surjectivity locus. -/
theorem surjectivityOpenSubspace_pointsSet [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    (surjectivityOpenSubspace f u).pointsSet = surjectivityLocus f u :=
  OpenSubspace.fromOpens_pointsSet (surjectivityOpens f u)

/-- A test morphism lands in the surjectivity locus if and only if the base change
of the module morphism is an epimorphism. -/
theorem mem_surjectivityLocus_iff [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] {T : Over S} (a : ofOver T ⟶ B) :
    Set.range (Points.map a) ⊆ surjectivityLocus f u ↔
      Epi (baseChangeMap f a u) :=
  sorry

/-- For a locally finitely presented morphism and a finite-type target module with
support proper over the base, a test morphism factors through the surjectivity open
subspace if and only if the base-changed module morphism is an epimorphism. -/
theorem factors_surjectivityOpenSubspace_iff [𝒢.IsFiniteType]
    [LocallyOfFinitePresentation f] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    {T : Over S} (a : ofOver T ⟶ B) :
    (∃ ℓ : ofOver T ⟶ (surjectivityOpenSubspace f u).X,
        ℓ ≫ (surjectivityOpenSubspace f u).ι = a) ↔
      Epi (baseChangeMap f a u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
