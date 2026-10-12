/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap67.Lemma_67_8_10_Pullback
public import stacks_project.Chap75.Lemma_75_3_1_Restrict
public import stacks_project.Chap75.Lemma_75_10_2_Sequence
public import stacks_project.Chap75.Lemma_75_19_1_Instances

/-!
# Mayer–Vietoris coreflection triangle on algebraic spaces

On an elementary distinguished square of quasi-compact quasi-separated algebraic
spaces, the quasicoherent coreflection of `D(𝒪_X)` sends the Mayer–Vietoris
pushforward triangle of Lemma 75.10.2 to a distinguished triangle, whose vertices
are identified with the source `Rf_* DQ` writing by Lemma 75.19.2.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The chosen right adjoint of the inclusion of derived modules with quasi-coherent
cohomology carries the canonical shift comparison induced by its adjunction. -/
noncomputable instance instCommShift_inclusion_rightAdjoint {S : Scheme.{u}}
    (X : AlgebraicSpace S) [(inclusion X).IsLeftAdjoint] :
    ((inclusion X).rightAdjoint).CommShift ℤ :=
  (Adjunction.ofIsLeftAdjoint (inclusion X)).rightAdjointCommShift ℤ

/-- The chosen right adjoint of the inclusion of derived modules with quasi-coherent
cohomology is a triangulated functor. -/
instance instIsTriangulated_inclusion_rightAdjoint {S : Scheme.{u}}
    (X : AlgebraicSpace S) [(inclusion X).IsLeftAdjoint] :
    ((inclusion X).rightAdjoint).IsTriangulated :=
  sorry

variable {S : Scheme.{u}} {U V X : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
variable [IsElementaryDistinguishedSquare j f]
variable [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
variable [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U]
variable [IsQuasiCompact V] [IsAbsolutelyQuasiSeparated V]

/-- The image of the Mayer–Vietoris pushforward triangle of Lemma 75.10.2 under the
exact endofunctor `(inclusion X).rightAdjoint ⋙ inclusion X` of `D(𝒪_X)`. -/
def mayerVietorisCoreflectionTriangle (K : ModuleDerived X) :
    Triangle (ModuleDerived X) :=
  ((inclusion X).rightAdjoint ⋙ inclusion X).mapTriangle.obj
    (mayerVietorisPushforwardTriangle j f K)

/-- The first vertex of the coreflection triangle is `DQ_X(K)` viewed in `D(𝒪_X)`. -/
theorem mayerVietorisCoreflectionTriangle_obj₁ (K : ModuleDerived X) :
    (mayerVietorisCoreflectionTriangle j f K).obj₁ =
      (inclusion X).obj ((inclusion X).rightAdjoint.obj K) :=
  sorry

/-- The second vertex of the coreflection triangle is the image of
`Rj_{U,*} (K|_U) ⊞ Rj_{V,*} (K|_V)` under `DQ_X`. -/
theorem mayerVietorisCoreflectionTriangle_obj₂ (K : ModuleDerived X) :
    (mayerVietorisCoreflectionTriangle j f K).obj₂ =
      ((inclusion X).rightAdjoint ⋙ inclusion X).obj
        (biprod ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj K))
          ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj K))) :=
  sorry

/-- The third vertex of the coreflection triangle is the image of
`Rj_{U ×_X V,*} (K|_{U ×_X V})` under `DQ_X`. -/
theorem mayerVietorisCoreflectionTriangle_obj₃ (K : ModuleDerived X) :
    (mayerVietorisCoreflectionTriangle j f K).obj₃ =
      ((inclusion X).rightAdjoint ⋙ inclusion X).obj
        ((pushforwardDerived (fiberHom j f)).obj
          ((restrictFunctorDerived (fiberHom j f)).obj K)) :=
  sorry

/-- After Lemma 75.19.2, the second vertex is isomorphic to
`Rj_{U,*} DQ_U(K|_U) ⊞ Rj_{V,*} DQ_V(K|_V)`. -/
theorem mayerVietorisCoreflectionTriangle_obj₂_isomorphic (K : ModuleDerived X) :
    IsIsomorphic (mayerVietorisCoreflectionTriangle j f K).obj₂
      (biprod
        ((pushforwardDerived j).obj
          ((inclusion U).obj
            ((inclusion U).rightAdjoint.obj ((restrictFunctorDerived j).obj K))))
        ((pushforwardDerived f).obj
          ((inclusion V).obj
            ((inclusion V).rightAdjoint.obj ((restrictFunctorDerived f).obj K))))) :=
  sorry

/-- After Lemma 75.19.2, the third vertex is isomorphic to
`Rj_{U ×_X V,*} DQ_{U ×_X V}(K|_{U ×_X V})`. -/
theorem mayerVietorisCoreflectionTriangle_obj₃_isomorphic (K : ModuleDerived X) :
    IsIsomorphic (mayerVietorisCoreflectionTriangle j f K).obj₃
      ((pushforwardDerived (fiberHom j f)).obj
        ((inclusion (pullback j f)).obj
          ((inclusion (pullback j f)).rightAdjoint.obj
            ((restrictFunctorDerived (fiberHom j f)).obj K)))) :=
  sorry

/-- The coreflection of the Mayer–Vietoris pushforward triangle is distinguished in
`D(𝒪_X)`. -/
theorem mayerVietorisCoreflectionTriangle_mem_distTriang (K : ModuleDerived X) :
    mayerVietorisCoreflectionTriangle j f K ∈ distTriang (ModuleDerived X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

