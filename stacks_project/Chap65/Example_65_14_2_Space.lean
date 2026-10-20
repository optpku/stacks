/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.Quotient

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

universe u

/- The concrete quotient sheaf. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.sheafOfPoints :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)))
