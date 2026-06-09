import Mathlib

variable {G : Type*} [Group G]

def IsCentralSeries (H : ℕ → Subgroup G) [∀ n, (H n).Normal] : Prop :=
  ∀ n, (⊤ : Subgroup (((H (n + 1))) ⧸ ((H n).subgroupOf (H (n + 1))))) ≤ ⊤

  -- Subgroup.comap (QuotientGroup.mk' (H n)) (Subgroup.center (G ⧸ (H n)))
