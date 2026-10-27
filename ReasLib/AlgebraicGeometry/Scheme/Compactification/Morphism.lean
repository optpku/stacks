/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- A morphism of compactifications commutes with the structure maps. -/
theorem ambientMap_comp_structure {S : Scheme.{u}} {X : Over S}
    {P Q : Of S X} (φ : P ⟶ Q) :
    ambientMap φ ≫ Q.obj.right.hom = P.obj.right.hom :=
  Over.w φ.hom.right

/-- The interior immersion of a compactification is separated. -/
instance instIsSeparated (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    IsSeparated (ι P) :=
  sorry

/-- The interior immersion of a compactification is locally quasi-finite. -/
instance instLocallyQuasiFinite (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    LocallyQuasiFinite (ι P) :=
  sorry

/-- The interior immersion of a compactification is locally of finite type. -/
instance instLocallyOfFiniteType (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    LocallyOfFiniteType (ι P) :=
  sorry

end AlgebraicGeometry.Scheme.Compactification.Of

end
