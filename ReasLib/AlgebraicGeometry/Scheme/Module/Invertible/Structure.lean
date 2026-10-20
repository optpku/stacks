module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Canonical invertible scheme modules

The canonical monoidal owner now equips every scheme-module category directly.
Consequently there is no separate mathematical notion of “some monoidal
structure making `L` invertible”: downstream declarations should use
`Scheme.Modules.Invertible L` itself.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u
