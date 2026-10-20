module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.CompactOpen

/-!
# Galois descent of quasi-compact opens of algebraic spaces

A quasi-compact open of an algebraic space after a possibly infinite Galois
field extension descends to a finite intermediate extension, and is stabilized
by an open subgroup of the Galois group.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

universe u

/- Lemma 72.12.6 (1): a quasi-compact open after a possibly infinite Galois field
extension descends to a finite intermediate field. -/
@[stacks 0A15]
#check
  (AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.CompactOpen.exists_finiteSubextension_preimage_eq :
    ∀ {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
      (X : AlgebraicSpace (Spec (of k)))
      (V : AlgebraicSpace.OpenSubspace (AlgebraicSpace.FieldExtension.baseChange k kbar X))
      [AlgebraicSpace.IsQuasiCompact V.X],
      ∃ (K' : IntermediateField k kbar) (_ : FiniteDimensional k K')
        (V' : AlgebraicSpace.OpenSubspace (AlgebraicSpace.FieldExtension.baseChange k K' X))
        (_ : AlgebraicSpace.IsQuasiCompact V'.X),
        AlgebraicSpace.FieldExtension.IsBaseChangeFromIntermediate K' V V')

/- Lemma 72.12.6 (2): a quasi-compact open after a possibly infinite Galois field
extension is stabilized by an open subgroup of the Galois group. -/
@[stacks 0A15]
#check
  (AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.CompactOpen.exists_openSubgroup_stabilizing :
    ∀ {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
      (X : AlgebraicSpace (Spec (of k)))
      (V : AlgebraicSpace.OpenSubspace (AlgebraicSpace.FieldExtension.baseChange k kbar X))
      [AlgebraicSpace.IsQuasiCompact V.X],
      ∃ (H : OpenSubgroup Gal(kbar/k)),
        ∀ σ : H,
          AlgebraicSpace.Points.map (AlgebraicSpace.FieldExtension.Galois.map k kbar X σ.1) ''
            V.pointsSet = V.pointsSet)
