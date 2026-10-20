module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity.BaseChange
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.EtaleVanishingCycles

@[expose] public section

universe u v

/- Lemma 59.93.4 (1). -/
@[stacks 0GJS] #check (AlgebraicGeometry.Scheme.locallyAcyclicAt_baseChange_of_locallyQuasiFinite :
    ∀ {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S),
    IsPullback g' f' f g →
    ∀ (K : Complexes X) (xbar' : GeometricPoint X')
    [LocallyOfFiniteType g] [LocallyQuasiFinite g],
    LocallyAcyclicAt f (xbar'.map g') K →
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K))

/- Lemma 59.93.4 (2). -/
@[stacks 0GJS] #check (AlgebraicGeometry.Scheme.locallyAcyclicAt_baseChange_of_affineTransitionLimit :
    ∀ {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S),
    IsPullback g' f' f g →
    ∀ (K : Complexes X) (xbar' : GeometricPoint X')
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D), IsLimit c →
    ∀ (e : c.pt ≅ S'),
    (∀ i : OrderDual I, c.π.app i ≫ t.app i = e.hom ≫ g) →
    ∀ [∀ i : OrderDual I, LocallyOfFiniteType (t.app i)]
    [∀ i : OrderDual I, LocallyQuasiFinite (t.app i)]
    [∀ {i j : OrderDual I} (q : i ⟶ j), IsAffineHom (D.map q)],
    LocallyAcyclicAt f (xbar'.map g') K →
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K))

/- Lemma 59.93.4 (3). -/
@[stacks 0GJS] #check (AlgebraicGeometry.Scheme.locallyAcyclicAt_baseChange_of_integral :
    ∀ {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S),
    IsPullback g' f' f g →
    ∀ (K : Complexes X) (xbar' : GeometricPoint X')
    [IsIntegralHom g],
    LocallyAcyclicAt f (xbar'.map g') K →
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K))
