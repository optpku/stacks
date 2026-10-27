/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Composition

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

universe u

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)

/- Compatible compactifications determine the pullback diagram used to compose lower shriek. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CompDiagram.of X g :
  (P_g : Of Z (Over.mk g)) →
    Of P_g.obj.right.left (Over.mk (X.hom ≫ Of.ι P_g)) → CompDiagram X g)

namespace CompDiagram

variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]

/-- The induced interior map of a compatible compactification diagram is an open immersion. -/
theorem instIsOpenImmersion_ιInterior (C : CompDiagram X g) :
    IsOpenImmersion (ιInterior X g C) :=
  isOpenImmersion_ιInterior X g C

/-- The induced interior map of a compatible compactification diagram is quasi-compact. -/
theorem instQuasiCompact_ιInterior (C : CompDiagram X g) :
    QuasiCompact (ιInterior X g C) :=
  quasiCompact_ιInterior X g C

/-- The projection from the pullback interior to the intermediate base is proper. -/
theorem instIsProper_toBase (C : CompDiagram X g) :
    IsProper (toBase X g C) :=
  isProper_toBase X g C

end CompDiagram

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek
