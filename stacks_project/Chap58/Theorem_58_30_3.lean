/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization.SmoothProper
public import ReasLib.Topology.Category.ProfiniteGrp.PrimeToP
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open ProfiniteGrp

universe u w

/- Theorem 58.30.3 (1): if `f : X ⟶ S` is smooth and proper with geometrically connected
fibres, and `s' ↝ s` is a specialization with `ringChar κ(s) = p` prime, then the étale
specialization map `π₁(X_{s̄'}) → π₁(X_{s̄})` is surjective. -/
@[stacks 0C0R] #check (EtaleFundamentalGroup.IsSpecializationMap.surjective_of_smooth_char :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (p : ℕ) (hp : Nat.Prime p)
    (hchar : ringChar (S.residueField sbar.image) = p)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp),
    Function.Surjective sp)

/- Theorem 58.30.3 (2): under the same hypotheses, the specialization map induces an
isomorphism of maximal prime-to-`p` quotients
`π₁'(X_{s̄'}) ≅ π₁'(X_{s̄})`. -/
@[stacks 0C0R] #check (EtaleFundamentalGroup.IsSpecializationMap.primeToPQuotientMap_bijective :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (p : ℕ) (hp : Nat.Prime p)
    (hchar : ringChar (S.residueField sbar.image) = p)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp),
    Function.Bijective
      (primeToPQuotientMap p (ProfiniteGrp.ofHom sp)))
