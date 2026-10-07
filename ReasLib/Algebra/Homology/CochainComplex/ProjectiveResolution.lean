module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Comparison.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Comparison.Iso
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.FixedBound
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Horseshoe

/-!
# Projective Resolutions of Cochain Complexes

Convenience import for bounded-above projective resolutions, additive strict and homotopy maps,
canonical comparison isomorphisms, fixed-bound specializations, and the projective horseshoe
construction. The canonical K-projective instances live with the definitions in
`ProjectiveResolution.Basic`.

It is distinct from mathlib's `CategoryTheory.ProjectiveResolution`, whose target is a single
object of an abelian category.
-/
