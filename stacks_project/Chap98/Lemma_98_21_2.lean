module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation
import StacksCheckRecall

/-!
# Infinitesimal and tangent functors of a deformation object

Under the strong Rim-Schlessinger condition, infinitesimal automorphisms and
lift classes define linear functors, with comparison isomorphisms and tangent actions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 98.21.2 (1). Infinitesimal automorphisms of trivial deformations form an
A-linear functor. For every square-zero S-algebra thickening with kernel I
and every lift x', its value at I is isomorphic to the relative infinitesimal
automorphisms of x'. -/
@[stacks 07Y9] #check (AlgebraicGeometry.GroupoidsOver.infFunctor :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)), ModuleCat.{u} A ⥤ ModuleCat.{u} A)

#check (AlgebraicGeometry.GroupoidsOver.infFunctor.instModuleLinear :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)), ModuleLinear (A : Type u) (infFunctor x))

#check (AlgebraicGeometry.GroupoidsOver.infIso :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA),
    (infFunctor x).obj (kernelObj fA) ≅ ModuleCat.of A (infinitesimalAut x'))

/- Lemma 98.21.2 (2). Isomorphism classes of lifts to trivial square-zero
extensions form an A-linear tangent functor. Its value at the kernel of any
square-zero S-algebra thickening acts on lift classes, simply transitively
when that set is nonempty. The quotient of lifts lies in Type (u + 1). -/
@[stacks 07Y9] #check (AlgebraicGeometry.GroupoidsOver.tangentFunctor :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)), ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A)

#check (AlgebraicGeometry.GroupoidsOver.tangentFunctor.instModuleLinear :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)), ModuleLinear (A : Type u) (tangentFunctor x))

#check (AlgebraicGeometry.GroupoidsOver.tangentForget :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A),
    ((tangentFunctor x).obj M : Type (u + 1)) ≃
      lifts x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M))

#check (AlgebraicGeometry.GroupoidsOver.tangentForget_bijective :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A),
    Function.Bijective (tangentForget x M))

#check (AlgebraicGeometry.GroupoidsOver.tangentAction :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)),
    (tangentFunctor x).obj (kernelObj fA) → lifts x fA hfA → lifts x fA hfA)

#check (AlgebraicGeometry.GroupoidsOver.tangentAction_zero :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (ξ : lifts x fA hfA),
    tangentAction x (0 : (tangentFunctor x).obj (kernelObj fA)) ξ = ξ)

#check (AlgebraicGeometry.GroupoidsOver.tangentAction_add :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA))
    (s t : (tangentFunctor x).obj (kernelObj fA)) (ξ : lifts x fA hfA),
    tangentAction x (s + t) ξ = tangentAction x s (tangentAction x t ξ))

#check (AlgebraicGeometry.GroupoidsOver.tangentAction_simplyTransitive :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) [Nonempty (lifts x fA hfA)]
    (ξ η : lifts x fA hfA),
    ∃! t : (tangentFunctor x).obj (kernelObj fA), tangentAction x t ξ = η)
