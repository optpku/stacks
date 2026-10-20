/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (FormallySmooth : {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
  (X ⟶ Y) → Prop)

#check (formallySmooth_iff : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
  (f : X ⟶ Y), FormallySmooth f ↔ Scheme.Over.FormallySmooth f)

#check (FormallySmooth.of : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
  {f : X ⟶ Y}, Scheme.Over.FormallySmooth f → FormallySmooth f)

#check (FormallySmooth.spec : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
  {f : X ⟶ Y} [FormallySmooth f], Scheme.Over.FormallySmooth f)

#check (FormallySmooth.id : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
  FormallySmooth (𝟙 X))

#check (FormallySmooth.toSchemeOver : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
  {f : X ⟶ Y} [FormallySmooth f], Scheme.Over.FormallySmooth f)

end AlgebraicGeometry.AlgebraicSpace
