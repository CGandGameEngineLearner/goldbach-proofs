(() => {
  const widget = document.querySelector('.presence-widget');
  if (!widget) return;
  const endpoint = new URL(widget.dataset.endpoint, document.baseURI);
  const cookiePath = new URL('../', endpoint).pathname;
  const visitors = widget.querySelector('[data-count="visitors"]');
  const agents = widget.querySelector('[data-count="agents"]');
  const views = widget.querySelector('[data-count="page_views"]');
  const ips = widget.querySelector('[data-count="unique_ips"]');
  const format = new Intl.NumberFormat(document.documentElement.lang);
  let visit;
  let timer;
  let pending = false;

  function visitorId() {
    // A short-lived first-party ID lets tabs share a visit, even behind a shared IP.
    try {
      visit = /(?:^|;\s*)goldbach_visit=([0-9a-f]{32})(?:;|$)/.exec(document.cookie)?.[1] || visit;
    } catch {}
    visit ||= crypto.randomUUID().replaceAll('-', '');
    try {
      document.cookie = `goldbach_visit=${visit}; Path=${cookiePath}; Max-Age=120; SameSite=Strict; Secure`;
    } catch {}
    return visit;
  }

  async function refresh() {
    if (pending || document.hidden) return;
    pending = true;
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 8000);
    try {
      const response = await fetch(endpoint, {
        method: 'POST', headers: { 'X-Goldbach-Visit': visitorId() },
        cache: 'no-store', signal: controller.signal
      });
      if (!response.ok) throw new Error('Presence unavailable');
      const value = await response.json();
      visitors.textContent = Number.isSafeInteger(value.visitors) ? format.format(value.visitors) : '—';
      agents.textContent = Number.isSafeInteger(value.agents) ? format.format(value.agents) : '—';
      views.textContent = Number.isSafeInteger(value.page_views) ? format.format(value.page_views) : '—';
      ips.textContent = Number.isSafeInteger(value.unique_ips) ? format.format(value.unique_ips) : '—';
    } catch {
      // Keep the last snapshot visible until the next heartbeat succeeds.
    } finally {
      clearTimeout(timeout);
      pending = false;
    }
  }

  function watch() {
    clearInterval(timer);
    if (!document.hidden) {
      refresh();
      timer = setInterval(refresh, 30000);
    }
  }
  widget.hidden = false;
  document.addEventListener('visibilitychange', watch);
  window.addEventListener('pagehide', () => clearInterval(timer));
  window.addEventListener('pageshow', watch);
  watch();
})();
