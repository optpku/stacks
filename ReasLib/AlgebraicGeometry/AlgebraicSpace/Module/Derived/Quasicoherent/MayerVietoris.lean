module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.Coreflection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence

/-!
# Mayer–Vietoris coreflection triangles on algebraic spaces

On an elementary distinguished square of quasi-compact quasi-separated algebraic
spaces, quasicoherent coreflection sends the derived Mayer–Vietoris pushforward
triangle to a distinguished triangle. Its vertices identify with the local
coreflections followed by derived pushforward.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {U V X : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
variable [IsElementaryDistinguishedSquare j f]
variable [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
variable [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U]
variable [IsQuasiCompact V] [IsAbsolutelyQuasiSeparated V]

/-- The image of the Mayer–Vietoris pushforward triangle under the
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
        (biprod ((moduleDerivedPushforward j).obj ((restrictFunctorDerived j).obj K))
          ((moduleDerivedPushforward f).obj ((restrictFunctorDerived f).obj K))) :=
  sorry

/-- The third vertex of the coreflection triangle is the image of
`Rj_{U ×_X V,*} (K|_{U ×_X V})` under `DQ_X`. -/
theorem mayerVietorisCoreflectionTriangle_obj₃ (K : ModuleDerived X) :
    (mayerVietorisCoreflectionTriangle j f K).obj₃ =
      ((inclusion X).rightAdjoint ⋙ inclusion X).obj
        ((moduleDerivedPushforward (fiberHom j f)).obj
          ((restrictFunctorDerived (fiberHom j f)).obj K)) :=
  sorry

/-- The second vertex of the coreflection triangle is isomorphic to
`Rj_{U,*} DQ_U(K|_U) ⊞ Rj_{V,*} DQ_V(K|_V)`. -/
theorem mayerVietorisCoreflectionTriangle_obj₂_isomorphic (K : ModuleDerived X) :
    IsIsomorphic (mayerVietorisCoreflectionTriangle j f K).obj₂
      (biprod
        ((moduleDerivedPushforward j).obj
          ((inclusion U).obj
            ((inclusion U).rightAdjoint.obj ((restrictFunctorDerived j).obj K))))
        ((moduleDerivedPushforward f).obj
          ((inclusion V).obj
            ((inclusion V).rightAdjoint.obj ((restrictFunctorDerived f).obj K))))) :=
  sorry

/-- The third vertex of the coreflection triangle is isomorphic to
`Rj_{U ×_X V,*} DQ_{U ×_X V}(K|_{U ×_X V})`. -/
theorem mayerVietorisCoreflectionTriangle_obj₃_isomorphic (K : ModuleDerived X) :
    IsIsomorphic (mayerVietorisCoreflectionTriangle j f K).obj₃
      ((moduleDerivedPushforward (fiberHom j f)).obj
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
