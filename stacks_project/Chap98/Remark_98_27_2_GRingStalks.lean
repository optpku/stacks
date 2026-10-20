/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GRingStalks

/-!
# Schemes with G-ring stalks

A scheme has G-ring stalks when every structure-sheaf stalk is a G-ring.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.HasGRingStalks : AlgebraicGeometry.Scheme.{u} → Prop)
