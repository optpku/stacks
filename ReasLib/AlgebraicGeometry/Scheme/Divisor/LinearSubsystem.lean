/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearSystem

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

namespace LinearSubsystem

/-- The projective scheme of the dual of a section subspace. -/
def scheme
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    SchemeOverField k :=
  Over.mk (ProjectiveSpace.VectorSpace.toSpec k (Module.Dual k V))

/-- The subsystem associated to `V` is the projective scheme of the `k`-linear dual of `V`. -/
theorem scheme_def
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    scheme X D V =
      Over.mk (ProjectiveSpace.VectorSpace.toSpec k (Module.Dual k V)) := sorry

/-- The map on symmetric algebras induced by restriction from all linear functionals to
functionals on `V` preserves the powers-of-degree-one gradings. -/
theorem gradedMap_mem
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    {n : ℕ} {x : SymmetricAlgebra k
      (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))}
    (hx : x ∈ ProjectiveSpace.VectorSpace.grading k
      (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) n) :
    SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι k (Module.Dual k V)).comp V.subtype.dualMap) x ∈
      ProjectiveSpace.VectorSpace.grading k (Module.Dual k V) n := sorry

/-- The graded symmetric-algebra map induced by dual restriction along `V.subtype`. -/
def gradedMap
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    ProjectiveSpace.VectorSpace.grading k
        (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) →+*ᵍ
      ProjectiveSpace.VectorSpace.grading k (Module.Dual k V) where
  toRingHom := (SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι k (Module.Dual k V)).comp V.subtype.dualMap)).toRingHom
  map_mem := gradedMap_mem X D V

/-- The underlying ring homomorphism of the subsystem graded map is induced by dual
restriction. -/
theorem gradedMap_toRingHom
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    (gradedMap X D V).toRingHom =
      (SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι k (Module.Dual k V)).comp V.subtype.dualMap)).toRingHom := sorry

/-- Dual restriction maps enough positive-degree elements to define the projective subsystem
morphism. -/
theorem gradedMap_irrelevant
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    HomogeneousIdeal.irrelevant (ProjectiveSpace.VectorSpace.grading k (Module.Dual k V)) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveSpace.VectorSpace.grading k
        (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)))).map
          (gradedMap X D V) := sorry

/-- The projective morphism induced by dual restriction commutes with the structure maps to
`Spec(k)`. -/
theorem projMap_toSpec
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    Proj.map (gradedMap X D V) (gradedMap_irrelevant X D V) ≫
        ProjectiveSpace.VectorSpace.toSpec k
          (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) =
      ProjectiveSpace.VectorSpace.toSpec k (Module.Dual k V) := sorry

/-- The morphism from the subsystem to the ambient projective model induced by restricting
linear functionals along `V.subtype`. -/
def inclusion
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    scheme X D V ⟶ CompleteLinearSystem.scheme X D :=
  Over.homMk
    (Proj.map (gradedMap X D V) (gradedMap_irrelevant X D V))
    (projMap_toSpec X D V)

/-- The underlying scheme morphism of the projective subsystem inclusion is the `Proj` map
induced by dual restriction. -/
theorem inclusion_left
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    (inclusion X D V).left =
      Proj.map (gradedMap X D V) (gradedMap_irrelevant X D V) := sorry

/-- The projective subsystem inclusion is a morphism over `Spec(k)`. -/
theorem inclusion_over
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    (inclusion X D V).left ≫ (CompleteLinearSystem.scheme X D).hom =
      (scheme X D V).hom := sorry

/-- The projective subsystem inclusion is a closed immersion. -/
theorem inclusion_isClosedImmersion
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    IsClosedImmersion (inclusion X D V).left := sorry

/-- The degree-one equations vanishing on `V`, namely the kernel of restriction from the dual
of the complete section space to the dual of `V`. -/
def equations
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    Submodule k (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :=
  LinearMap.ker V.subtype.dualMap

/-- A linear functional is an equation of the subsystem exactly when it vanishes after
restriction to `V`. -/
theorem mem_equations
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    (f : Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    f ∈ equations X D V ↔ V.subtype.dualMap f = 0 := sorry

/-- The homogeneous ideal generated by the degree-one equations vanishing on `V`. -/
def equationIdeal
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    Ideal (SymmetricAlgebra k
      (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))) :=
  Ideal.span (SymmetricAlgebra.ι k
    (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) ''
      (equations X D V : Set
        (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))))

/-- The equation ideal unfolds to the span of the images of the degree-one equations. -/
theorem equationIdeal_def
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    equationIdeal X D V =
      Ideal.span (SymmetricAlgebra.ι k
        (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) ''
          (equations X D V : Set
            (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)))) := sorry

/-- The kernel ideal defining the projective subsystem is generated by its degree-one
equations. -/
theorem gradedMap_ker
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) :
    RingHom.ker (gradedMap X D V).toRingHom = equationIdeal X D V := sorry

/-- The section subspace recovered from a space of linear equations is its dual
coannihilator. -/
def sectionSubspaceOfEquations
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (equations : Submodule k
      (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))) :
    Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf) :=
  equations.dualCoannihilator

/-- A section belongs to the subspace recovered from equations exactly when every equation
vanishes on it. -/
theorem mem_sectionSubspaceOfEquations
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (equations : Submodule k
      (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)))
    (s : Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf) :
    s ∈ sectionSubspaceOfEquations X D equations ↔ ∀ f ∈ equations, f s = 0 := sorry

/-- In finite dimension, section subspaces and spaces of linear equations determine one another. -/
theorem equations_iff
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    [FiniteDimensional k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    (equations : Submodule k
      (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))) :
    LinearSubsystem.equations X D V = equations ↔
      V = sectionSubspaceOfEquations X D equations := sorry

/-- The numerical projective-space index attached to a section subspace. -/
def projectiveIndex
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)) : ℕ :=
  Module.finrank k V - 1

/-- For a nonzero finite-dimensional section subspace, projective-space index `r` is equivalent
to vector-space dimension `r + 1`. -/
theorem projectiveIndex_eq_iff
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    [FiniteDimensional k V] (hV : 0 < Module.finrank k V) (r : ℕ) :
    projectiveIndex X D V = r ↔ Module.finrank k V = r + 1 := sorry

/-- A nonempty subsystem has geometric dimension `r` exactly when its section subspace has
dimension `r + 1`. -/
theorem dimension_eq_iff_finrank_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    [FiniteDimensional k V] (hV : 0 < Module.finrank k V) (r : ℕ) :
    topologicalKrullDim (scheme X D V).left = r ↔
      Module.finrank k V = r + 1 := sorry

end LinearSubsystem

end AlgebraicGeometry.Scheme.IdealSheafData
