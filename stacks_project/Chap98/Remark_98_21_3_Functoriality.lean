module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.Functoriality
import StacksCheckRecall

/-!
# Functoriality of infinitesimal and tangent modules

Under condition (RS*), a ring map `A ⟶ B` with `y = x|_Spec(B)` and an
`A`-linear map `M ⟶ N` induce a pullback of lift categories along
`A[M] ⟶ B[N]`, hence `A`-linear maps `Inf_x(M) ⟶ Inf_y(N)` and
`T_x(M) ⟶ T_y(N)`. A morphism of deformation situations likewise yields a
pullback of lifts, and the Inf comparison and tangent action are natural in
the square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver

open scoped Bicategory

universe u

/- Remark 98.21.3 (Functoriality) (1). Assumptions and notation as in
Lemma 98.21.2. A ring map `A ⟶ B` with a fibre morphism `φ : x|_Spec(B) ⟶ y`
and a commutative square of `S`-algebra thickenings induce a pullback functor
`Lift(x, A') ⥤ Lift(y, B')`. The identity `φ` recovers `y = x|_Spec(B)`, and
the trivial-square-zero square specialises this to
`Lift(x, A[M]) ⥤ Lift(y, B[N])`. Lean records the pullback as `liftPullback`. -/
@[stacks 07YA] #check (AlgebraicGeometry.GroupoidsOver.liftPullback :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y),
liftCat x fA hfA ⥤ liftCat y fB hfB)

/- Remark 98.21.3 (Functoriality) (2). The same data with an `A`-linear map
`M ⟶ N` induce a canonical `A`-linear map `Inf_x(M) ⟶ Inf_y(N)`, recorded as
`infMap`. -/
@[stacks 07YA] #check (AlgebraicGeometry.GroupoidsOver.infMap :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y),
(infFunctor x).obj M ⟶
      (ModuleCat.restrictScalars v.hom).obj ((infFunctor y).obj N))

/- Remark 98.21.3 (Functoriality) (3). The same data induce a canonical
`A`-linear map `T_x(M) ⟶ T_y(N)`, recorded as `tangentMap`. -/
@[stacks 07YA] #check (AlgebraicGeometry.GroupoidsOver.tangentMap :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y),
(tangentFunctor x).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} v.hom).obj ((tangentFunctor y).obj N))

/- Remark 98.21.3 (Functoriality) (4). For a square-zero thickening `A' ⟶ A`
with kernel `I`, a given lift `x'` of `x` to `A'` (which may not always exist),
and `y'` the pullback of `x'`, the diagram comparing `Inf_x(I) ≅ Inf(x'/x)`
with `Inf_y(J) ≅ Inf(y'/y)` commutes. Lean records this as `infIso_natural`. -/
@[stacks 07YA] #check (AlgebraicGeometry.GroupoidsOver.infIso_natural :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (x' : liftCat x fA hfA),
(infIso x x').hom ≫
        infinitesimalAutRestrict fA hfA fB hfB v hv u hu sq x y φ x' =
      infMap v hv (kernelHom fA fB v u sq) x y φ ≫
        (ModuleCat.restrictScalars v.hom).map
          (infIso y ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).obj x')).hom)

/- Remark 98.21.3 (Functoriality) (5). The action `T_x(I) × Lift(x, A') ⟶
Lift(x, A')` is natural in the same square, recorded as
`tangentAction_natural`. -/
@[stacks 07YA] #check (AlgebraicGeometry.GroupoidsOver.tangentAction_natural :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (t : (tangentFunctor x).obj (kernelObj fA))
    (ξ : lifts x fA hfA),
liftsMap (liftPullback fA hfA fB hfB v hv u hu sq x y φ) (tangentAction x t ξ) =
      tangentAction y (tangentMap v hv (kernelHom fA fB v u sq) x y φ t)
        (liftsMap (liftPullback fA hfA fB hfB v hv u hu sq x y φ) ξ))
