module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.QuasiCompact
import StacksCheckRecall

/-!
# Quasi-compact morphisms induce quasi-compact maps on points

A quasi-compact morphism of algebraic spaces induces a quasi-compact map of
underlying point spaces: inverse images of quasi-compact opens are quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.8.3: Let `S` be a scheme. If `f : X ⟶ Y` is a quasi-compact morphism
of algebraic spaces over `S`, then the underlying map `|f| : |X| ⟶ |Y|` of
topological spaces is quasi-compact. -/
@[stacks 0EMK] #check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.isSpectralMap :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f] →
      IsSpectralMap (AlgebraicGeometry.AlgebraicSpace.Points.map f))

#check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.isCompact_preimage :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f] →
      ∀ {V : Set (AlgebraicGeometry.AlgebraicSpace.Points Y)}, IsOpen V → IsCompact V →
        IsCompact (AlgebraicGeometry.AlgebraicSpace.Points.map f ⁻¹' V))
