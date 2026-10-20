module

public import ReasLib.RingTheory.Flatness.Tor

/-!
# Legacy Flatness-Through-`Tor` Import

The canonical `Tor` criteria for flatness are owned by `Module.Flat` in
`ReasLib.RingTheory.Flatness.Tor`.  This path remains as an import-only compatibility leaf while
category-specific change-of-rings APIs are separated from flatness itself.
-/

@[expose] public section
