/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.RHom.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.1

The degree-zero cohomology comparison for the derived internal Hom is owned by the reusable
`RingedSite.Hom.ModuleDerived.InternalHom.Cohomology` API.  This chapter file is a recall surface:
it keeps the objectwise and global source clauses separate while importing only their ReasLib leaf.
-/

open CategoryTheory
open RingedSite.Hom.ModuleDerived.InternalHom.Cohomology

/- Lemma 21.35.1 (08JA) (1): for `U : X`, `H^0(U, RHom(L, M))` identifies with the morphism group
in the derived category of the localization at `U`. -/
@[stacks 08JA "objectwise derived internal-Hom cohomology"] #check
  @objectwiseH0_isomorphic_localizedHom

/- Lemma 21.35.1 (08JA) (2): global degree-zero cohomology of `RHom(L, M)` identifies with the
morphism group in the derived category on `X`. -/
@[stacks 08JA "global derived internal-Hom cohomology"] #check
  @globalH0_isomorphic_derivedHom
