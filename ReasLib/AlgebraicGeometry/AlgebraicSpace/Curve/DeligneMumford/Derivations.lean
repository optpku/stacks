/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials

/-!
# The Deligne–Mumford locus and vanishing derivations

For proper schemes of dimension at most one over a field, membership in the
Deligne–Mumford locus is equivalent to vanishing of relative sheaf derivations
of the structure sheaf into itself.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- For a proper scheme of dimension at most one over a field, membership in
the Deligne–Mumford locus, geometric reducedness and dimension zero of its
automorphism space, unramifiedness of that space, and vanishing of relative
sheaf derivations of the structure sheaf into itself are equivalent. -/
theorem classifying_factorsThrough_dm_tfae_scheme_derivations
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    List.TFAE
      [dm (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        (∀ G : AlgebraicSpace (Spec (CommRingCat.of k)),
          IsRepresentedBy (mkOfSchemeOverField X hdim) G →
            GeometricallyReduced G ∧ dimension G = 0),
        IsUnramified (mkOfSchemeOverField X hdim),
        Subsingleton
          (RingedSpace.Hom.derivations X.hom.toShHom
            (SheafOfModules.unit X.left.toRingedSpace.ringCatSheaf))] :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
