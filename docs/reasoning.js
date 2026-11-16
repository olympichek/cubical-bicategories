(() => {
  const control = document.getElementById("reasoning-control");
  const checkbox = document.getElementById("show-justifications");
  const openers = new Set(["≡⟨", "≡˘⟨", "≡["]);
  const closers = new Set(["⟩", "⟩≡", "⟩∎"]);

  function markSteps(block) {
    const stack = [];
    // Agda links all pieces of a mixfix operator to the same definition.
    for (const token of block.querySelectorAll(":scope > a.Function[href]")) {
      const href = token.getAttribute("href");
      if (!/^(Cubical\.Foundations\.Prelude|Bicategories\.PathReasoning)\.html#\d+$/.test(href)) continue;
      // Leave the definition of the notation itself readable.
      if (token.pathname === location.pathname) continue;
      if (openers.has(token.textContent)) {
        stack.push(token);
        continue;
      }
      const start = stack[stack.length - 1];
      if (!closers.has(token.textContent) || !start || start.getAttribute("href") !== href) continue;
      stack.pop();

      const range = document.createRange();
      range.setStartBefore(start);
      range.setEndAfter(token);
      const step = document.createElement("span");
      step.className = "reasoning-step";
      range.surroundContents(step);
      const marker = document.createElement("span");
      marker.className = "reasoning-equality";
      marker.textContent = "≡";
      step.before(marker);
    }
  }

  for (const block of document.querySelectorAll("pre.Agda")) markSteps(block);
  if (!document.querySelector(".reasoning-step")) return;

  const key = "cubical-bicategories:" + new URL(".", location.href).pathname + ":show-justifications";
  function showJustifications(show) {
    document.documentElement.classList.toggle("hide-justifications", !show);
    checkbox.checked = show;
  }

  checkbox.addEventListener("change", () => {
    showJustifications(checkbox.checked);
    try { localStorage.setItem(key, String(checkbox.checked)); } catch { /* Storage is optional. */ }
  });

  function revealFragment(hash) {
    if (!hash || checkbox.checked) return;
    let id;
    try { id = decodeURIComponent(hash.slice(1)); } catch { return; }
    const target = document.getElementById(id);
    if (target && target.closest(".reasoning-step")) {
      showJustifications(true);
      target.scrollIntoView();
    }
  }

  function restoreView() {
    let preferred = false;
    try { preferred = localStorage.getItem(key) === "true"; } catch { /* Storage is optional. */ }
    showJustifications(preferred);
    revealFragment(location.hash);
  }

  restoreView();
  control.hidden = false;
  window.addEventListener("pageshow", event => {
    if (event.persisted) restoreView();
  });
  window.addEventListener("hashchange", () => revealFragment(location.hash));
  document.addEventListener("click", event => {
    // Clicking the current fragment again does not fire hashchange.
    const link = event.target instanceof Element && event.target.closest("a[href]");
    if (link && link.hash === location.hash && link.origin === location.origin &&
        link.pathname === location.pathname && link.search === location.search) {
      revealFragment(link.hash);
    }
  });
})();
