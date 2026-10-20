/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H

/-!
# Local Noetherianity of h coverings

Members of an h covering are locally of finite presentation, and their sources
are locally Noetherian when the base is locally Noetherian.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

/-- Each member of an h covering is locally of finite presentation. -/
instance HCovering.instLocallyOfFinitePresentation {T : Scheme.{u}} {ι : Type v}
    {family : ι → Over T} [h : HCovering family] (i : ι) :
    LocallyOfFinitePresentation (family i).hom :=
  h.locallyOfFinitePresentation i

/-- Sources of an h covering of a locally Noetherian scheme are locally Noetherian. -/
instance HCovering.instIsLocallyNoetherian {S : Scheme.{u}} [IsLocallyNoetherian S]
    {ι : Type v} {family : ι → Over S} [HCovering family] (i : ι) :
    IsLocallyNoetherian (family i).left :=
  LocallyOfFiniteType.isLocallyNoetherian (family i).hom

end AlgebraicGeometry.Scheme
