/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/- The reusable declarations are owned by `ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing`.
The typed checks below preserve this source-facing module as an importable bridge. -/
#check (AlgebraicGeometry.Scheme.etaleLocalRing :
    ∀ (S : Scheme.{u}) (s : GeometricPoint S), Type u)
#check (AlgebraicGeometry.Scheme.etaleLocalRing.fromZariskiStalk :
    ∀ (S : Scheme.{u}) (s : GeometricPoint S),
      S.presheaf.stalk s.image →+* etaleLocalRing S s)
#check (AlgebraicGeometry.Scheme.etaleLocalRing.isStrictHenselizationOf :
    ∀ (S : Scheme.{u}) (s : GeometricPoint S),
      IsStrictHenselizationOf (S.presheaf.stalk s.image) (etaleLocalRing.asAlgebra S s))

/-- Preserve the historical callable name for the strict-henselization instance. -/
abbrev etaleLocalRing.instIsStrictHenselizationOf
    (S : Scheme.{u}) (s : GeometricPoint S) :
    IsStrictHenselizationOf (S.presheaf.stalk s.image) (etaleLocalRing S s) :=
  @AlgebraicGeometry.Scheme.Etale.stalkRing.isStrictHenselizationOf S s.K inferInstance
    (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom

end AlgebraicGeometry.Scheme
