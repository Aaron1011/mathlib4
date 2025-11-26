import Mathlib

structure IsoData {n: ℕ} {G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)} (g: G) where
  a : ℕ
  ha: a ≠ 0
  A: Subgroup (Matrix.unitaryGroup (Fin a) ℂ)
  B: Subgroup (Matrix.unitaryGroup (Fin (n - a)) ℂ)
  iso: Subgroup.centralizer {g} ≃* A × B

lemma diag_of_eigenspace_span {n: ℕ} [hn: NeZero n] (g: ((Fin n) → ℂ) →ₗ[ℂ] (Fin n) → ℂ) (k: ℂ) (hg: Module.End.eigenspace g k = ⊤):
  g = k • 1 := by

  rw [LinearMap.ext_iff]
  intro x
  simp

  have has_eigenvalue: Module.End.HasEigenvalue g k := by
    rw [Module.End.hasEigenvalue_iff, hg]
    simp

  have x_mem: x ∈ Module.End.eigenspace g k := by
    simp [hg]

  rw [Module.End.mem_eigenspace_iff] at x_mem
  exact x_mem

lemma centralizer_iso {n: ℕ} [hn: NeZero n] (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g: G) (g_not: ∀ z: ℂ, g.val.val ≠ z • 1):
    Nonempty (IsoData g) := by



  obtain ⟨k, hk⟩ := Module.End.exists_eigenvalue g.val.val.toLin'
  by_cases eigenspace_top: Module.End.eigenspace g.val.val.toLin' k = ⊤
  .
    have eq_diag := diag_of_eigenspace_span g.val.val.toLin' k eigenspace_top
    specialize g_not k
    apply_fun (fun f => f.toMatrix') at eq_diag
    simp at eq_diag
    contradiction
  .
    have span := Module.End.iSup_maxGenEigenspace_eq_top g.val.val.toLin'
    rw [iSup_split_single _ k] at span
    rw [← codisjoint_iff] at span

    have other_ne_bot := Codisjoint.ne_bot_of_ne_top span eigenspace_top


  let f: Subgroup.centralizer {g} ≃* A × B := {

  }
  sorry
