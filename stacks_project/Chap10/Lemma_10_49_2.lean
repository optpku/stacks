module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Integral
import StacksCheckRecall

universe u

@[expose] public section

/-!
# Geometrically Integral Algebras

@stack 05DY

Lemma 10.49.2 is a canonical check of the shared affine bridge between
geometric integrality, geometric irreducibility, and ring-level geometric
reducedness.
-/

/- Lemma 10.49.2 (Tag 05DY): a `k`-algebra is geometrically integral exactly when it is
geometrically irreducible over `k` and geometrically reduced over `k`. -/
@[stacks 05DY]
#check
  (AlgebraicGeometry.SchemeOverField.GeometricallyIntegral.spec_iff :
    ∀ {k S : Type u} [Field k] [CommRing S] [Algebra k S],
      AlgebraicGeometry.GeometricallyIntegral
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k S))) ↔
        AlgebraicGeometry.GeometricallyIrreducible
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k S))) ∧
          Algebra.IsGeometricallyReduced k S)
