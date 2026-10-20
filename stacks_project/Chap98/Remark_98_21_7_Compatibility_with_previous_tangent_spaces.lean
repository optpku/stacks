module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.PredeformationComparison
import StacksCheckRecall

/-!
# Compatibility with previous tangent spaces

Under condition (RS*), the predeformation tangent space `Tℱ_{X,k,x0}` and the
infinitesimal automorphism group `Inf(ℱ_{X,k,x0})` of `98.8.0.1` and `98.8.0.2`
agree as `k`-vector spaces with the RS* modules `T_{x0}(k)` and `Inf_{x0}(k)`
of Lemma 98.21.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation

noncomputable section

universe u

/- Remark 98.21.7 (Compatibility with previous tangent spaces) (1). Let `S` be a
locally Noetherian scheme, let `X` be a category fibred in groupoids over
`(Sch/S)_fppf` satisfying (RS*), let `k` be a field of finite type over `S`, and
let `x0` be an object of `X` over `Spec(k)`. Then `Tℱ_{X,k,x0} = T_{x0}(k)` as
`k`-vector spaces, where the left-hand side is the dual-number fibre of
`ℱ_{X,k,x0}` as in `98.8.0.1` and the right-hand side is the value of
`tangentFunctor` at `k`. Lean records the identification as `tangentSpaceEquiv`. -/
@[stacks 0D18] #check (AlgebraicGeometry.GroupoidsOver.Predeformation.tangentSpaceEquiv :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
      {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
      (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))
      [hRS : HasStrongRimSchlessinger X],
    CategoryTheory.Functor.tangentSpace
        (predeformationFunctor X openImmersion kToS h_factor x0) ≃ₗ[k]
      ((tangentFunctor x0).obj (ModuleCat.of k k) : Type (u + 1)))

/- Remark 98.21.7 (Compatibility with previous tangent spaces) (2). In the same
setting, `Inf(ℱ_{X,k,x0}) = Inf_{x0}(k)` as `k`-vector spaces, where the
left-hand side is the kernel of restriction on automorphisms of a cartesian
dual-number pullback as in `98.8.0.2` and the right-hand side is the value of
`infFunctor` at `k`. Lean records the identification as `infinitesimalAutEquiv`. -/
@[stacks 0D18] #check (AlgebraicGeometry.GroupoidsOver.Predeformation.infinitesimalAutEquiv :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
      {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
      (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))
      [hRS : HasStrongRimSchlessinger X],
    (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) ≃ₗ[k]
      ((infFunctor x0).obj (ModuleCat.of k k) : Type u))
