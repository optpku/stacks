/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import Mathlib.AlgebraicGeometry.Spec

open CategoryTheory AlgebraicGeometry

universe u v

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The spectrum of an arbitrary intrinsic strict henselization of the Zariski local ring
at the image of a geometric point. No compatible residue-field embedding is specified. -/
def strictHenselizationScheme (S : Scheme.{u}) (s : GeometricPoint S) (Rsh : Type v)
    [CommRing Rsh] [Algebra (S.presheaf.stalk s.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh] : Scheme.{v} :=
  Spec (CommRingCat.of Rsh)

/-- The strict henselization scheme is definitionally the spectrum of the chosen
strict henselization ring. -/
theorem strictHenselizationScheme_def
    (S : Scheme.{u}) (s : GeometricPoint S) (Rsh : Type v)
    [CommRing Rsh] [Algebra (S.presheaf.stalk s.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh] :
    strictHenselizationScheme S s Rsh = Spec (CommRingCat.of Rsh) := sorry

/-- The henselization scheme of a point is the spectrum of a chosen henselization
of the Zariski local ring at that point. -/
def henselizationScheme (S : Scheme.{u}) (x : S) (Rh : Type v)
    [CommRing Rh] [Algebra (S.presheaf.stalk x) Rh]
    [IsHenselizationOf (S.presheaf.stalk x) Rh] : Scheme.{v} :=
  Spec (CommRingCat.of Rh)

/-- The henselization scheme is definitionally the spectrum of the chosen
henselization ring. -/
theorem henselizationScheme_def
    (S : Scheme.{u}) (x : S) (Rh : Type v)
    [CommRing Rh] [Algebra (S.presheaf.stalk x) Rh]
    [IsHenselizationOf (S.presheaf.stalk x) Rh] :
    henselizationScheme S x Rh = Spec (CommRingCat.of Rh) := sorry

/-- The strict henselization scheme at a geometric point is the spectrum of its étale local
ring. -/
def strictHenselizationAt (S : Scheme.{u}) (s : GeometricPoint S) : Scheme.{u} :=
  Spec (etaleLocalRing.asCommRing S s)

/-- The strict henselization scheme at a geometric point is definitionally the spectrum of its
étale local ring. -/
theorem strictHenselizationAt_def (S : Scheme.{u}) (s : GeometricPoint S) :
    strictHenselizationAt S s = Spec (etaleLocalRing.asCommRing S s) := sorry

/-- The canonical morphism from the strict henselization scheme at `sbar` to `S`. -/
noncomputable def strictHenselizationMap (S : Scheme.{u}) (sbar : Scheme.GeometricPoint S)
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh] :
    strictHenselizationScheme S sbar Rsh ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk sbar.image) Rsh)) ≫
    S.fromSpecStalk sbar.image

/-- The strict-henselization map is the composite induced by the stalk algebra map and
`Scheme.fromSpecStalk`. -/
theorem strictHenselizationMap_def (S : Scheme.{u}) (sbar : Scheme.GeometricPoint S)
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh] :
    strictHenselizationMap S sbar Rsh =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk sbar.image) Rsh)) ≫
        S.fromSpecStalk sbar.image := sorry

end AlgebraicGeometry.Scheme
