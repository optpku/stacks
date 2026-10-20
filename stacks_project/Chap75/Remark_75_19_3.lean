module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.MayerVietoris
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

/- Remark 75.19.3: Let `S` be a scheme. Let `(j : U ⟶ X, f : V ⟶ X)` be an
elementary distinguished square of algebraic spaces over `S`. Assume `X`, `U`, and
`V` are quasi-compact and quasi-separated. By Lemma 75.19.1 the functors
`(inclusion X).rightAdjoint`, `(inclusion U).rightAdjoint`,
`(inclusion V).rightAdjoint`, and `(inclusion (pullback j f)).rightAdjoint` exist.
Moreover, for every `K` in `D(𝒪_X)` there is a canonical distinguished triangle
`(inclusion X).obj ((inclusion X).rightAdjoint.obj K) ⟶
Rj_{U,*} ((inclusion U).obj ((inclusion U).rightAdjoint.obj (K|_U))) ⊞
Rj_{V,*} ((inclusion V).obj ((inclusion V).rightAdjoint.obj (K|_V))) ⟶
Rj_{U ×_X V,*} ((inclusion (pullback j f)).obj
((inclusion (pullback j f)).rightAdjoint.obj (K|_{U ×_X V}))) ⟶`
obtained by applying the exact functor `(inclusion X).rightAdjoint ⋙ inclusion X`
to the distinguished triangle of Lemma 75.10.2 and identifying vertices via
Lemma 75.19.2. -/
@[stacks 0CR6] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.mayerVietorisCoreflectionTriangle_mem_distTriang :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
      (f : V ⟶ X) [Etale f] [IsElementaryDistinguishedSquare j f]
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U]
      [IsQuasiCompact V] [IsAbsolutelyQuasiSeparated V]
      (K : ModuleDerived X),
      mayerVietorisCoreflectionTriangle j f K ∈ distTriang (ModuleDerived X))

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.mayerVietorisCoreflectionTriangle_obj₁ :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
      (f : V ⟶ X) [Etale f] [IsElementaryDistinguishedSquare j f]
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U]
      [IsQuasiCompact V] [IsAbsolutelyQuasiSeparated V]
      (K : ModuleDerived X),
      (mayerVietorisCoreflectionTriangle j f K).obj₁ =
        (inclusion X).obj ((inclusion X).rightAdjoint.obj K))

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.mayerVietorisCoreflectionTriangle_obj₂_isomorphic :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
      (f : V ⟶ X) [Etale f] [IsElementaryDistinguishedSquare j f]
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U]
      [IsQuasiCompact V] [IsAbsolutelyQuasiSeparated V]
      (K : ModuleDerived X),
      IsIsomorphic (mayerVietorisCoreflectionTriangle j f K).obj₂
        (biprod
          ((moduleDerivedPushforward j).obj
            ((inclusion U).obj
              ((inclusion U).rightAdjoint.obj ((restrictFunctorDerived j).obj K))))
          ((moduleDerivedPushforward f).obj
            ((inclusion V).obj
              ((inclusion V).rightAdjoint.obj ((restrictFunctorDerived f).obj K))))))

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.mayerVietorisCoreflectionTriangle_obj₃_isomorphic :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
      (f : V ⟶ X) [Etale f] [IsElementaryDistinguishedSquare j f]
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U]
      [IsQuasiCompact V] [IsAbsolutelyQuasiSeparated V]
      (K : ModuleDerived X),
      IsIsomorphic (mayerVietorisCoreflectionTriangle j f K).obj₃
        ((moduleDerivedPushforward (fiberHom j f)).obj
          ((inclusion (pullback j f)).obj
            ((inclusion (pullback j f)).rightAdjoint.obj
              ((restrictFunctorDerived (fiberHom j f)).obj K)))))
