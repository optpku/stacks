module

public import stacks_project.Chap59.Definition_59_93_1_LocalAcyclicity
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Tactic.CrossRefAttribute

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

@[expose] public section

universe u v w

namespace AlgebraicGeometry.Scheme

open EtaleVanishingCycles

/-- Lemma 59.93.4 (1): local acyclicity at a geometric point is inherited along a cartesian
square when the base change morphism `g` is locally quasi-finite. -/
@[stacks 0GJS]
theorem locallyAcyclicAt_baseChange_of_locallyQuasiFinite
    {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g)
    (K : Complexes X) (xbar' : GeometricPoint X')
    [LocallyQuasiFinite g]
    (h : LocallyAcyclicAt f (xbar'.imageHom g') K) :
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K) :=
  sorry

/-- Lemma 59.93.4 (2): local acyclicity at a geometric point is inherited along a cartesian
square when `S'` is a directed inverse limit of locally quasi-finite `S`-schemes with affine
transition maps, identified with the given morphism `g`. -/
@[stacks 0GJS]
theorem locallyAcyclicAt_baseChange_of_affineTransitionLimit
    {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g)
    (K : Complexes X) (xbar' : GeometricPoint X')
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (e : c.pt ≅ S')
    (he : ∀ i : OrderDual I, c.π.app i ≫ t.app i = e.hom ≫ g)
    [∀ i : OrderDual I, LocallyQuasiFinite (t.app i)]
    [∀ {i j : OrderDual I} (q : i ⟶ j), IsAffineHom (D.map q)]
    (h : LocallyAcyclicAt f (xbar'.imageHom g') K) :
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K) :=
  sorry

/-- Lemma 59.93.4 (3): local acyclicity at a geometric point is inherited along a cartesian
square when the base change morphism `g` is integral. -/
@[stacks 0GJS]
theorem locallyAcyclicAt_baseChange_of_integral
    {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g)
    (K : Complexes X) (xbar' : GeometricPoint X')
    [IsIntegralHom g]
    (h : LocallyAcyclicAt f (xbar'.imageHom g') K) :
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K) :=
  sorry

end AlgebraicGeometry.Scheme
