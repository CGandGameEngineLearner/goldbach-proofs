const logoForm = document.querySelector('#logo-upload');
if (logoForm) {
  const input = logoForm.elements.logo;
  const feedback = logoForm.querySelector('[role="alert"]');
  const button = logoForm.querySelector('button');
  const zh = document.documentElement.lang === 'zh';
  const label = button.textContent;
  const t = (chinese, english) => zh ? chinese : english;

  function showError(message, signIn = false) {
    feedback.textContent = message;
    if (signIn) {
      const link = document.createElement('a');
      link.href = '/auth/zhihu/sponsors?lang=' + (zh ? 'zh' : 'en');
      link.textContent = t('打开登录页', 'Open the sign-in page');
      feedback.append(' ', link);
    }
    feedback.hidden = false;
  }

  function validSize() {
    feedback.hidden = true;
    if (input.files[0]?.size > Number(logoForm.dataset.maxBytes)) {
      showError(t('文件超过 4 MiB，请压缩或换一张图片。', 'The file exceeds 4 MiB. Compress it or choose another image.'));
      return false;
    }
    return true;
  }

  input.addEventListener('change', validSize);
  logoForm.addEventListener('submit', async (event) => {
    event.preventDefault();
    if (button.disabled || !validSize()) return;
    button.disabled = true;
    button.textContent = t('正在提交…', 'Submitting…');
    const fallback = t('提交未完成，请检查连接后重试。', 'Submission incomplete. Check your connection and retry.');
    try {
      const result = await fetch(logoForm.action, {
        method: 'POST',
        body: new FormData(logoForm),
        signal: AbortSignal.timeout(30000),
      });
      if (result.ok && result.redirected) {
        location.assign(result.url);
        return;
      }
      const response = new DOMParser().parseFromString(await result.text(), 'text/html');
      showError(response.querySelector('[role="alert"]')?.textContent || fallback, result.status === 403);
    } catch {
      showError(fallback);
    } finally {
      button.disabled = false;
      button.textContent = label;
    }
  });
}

const orderForm = document.querySelector('#sponsor-order');
if (orderForm) {
  const list = document.querySelector('#sponsor-sort-list');
  const save = orderForm.querySelector('button');
  const original = orderForm.elements.original.value;
  let dragged = null;

  function updateOrder() {
    const entries = [...list.children];
    for (const [index, entry] of entries.entries()) {
      entry.querySelector('[data-move="-1"]').setAttribute('aria-disabled', index === 0);
      entry.querySelector('[data-move="1"]').setAttribute('aria-disabled', index === entries.length - 1);
    }
    const order = entries.map(entry => entry.dataset.sponsorId).join(',');
    orderForm.elements.order.value = order;
    save.disabled = order === original;
  }

  list.addEventListener('dragstart', (event) => {
    if (!event.target.matches('.drag-handle')) return;
    dragged = event.target.closest('.submission');
    event.dataTransfer.setData('text/plain', dragged.dataset.sponsorId);
    event.dataTransfer.effectAllowed = 'move';
    dragged.classList.add('dragging');
  });
  list.addEventListener('dragover', (event) => {
    if (!dragged) return;
    event.preventDefault();
    event.dataTransfer.dropEffect = 'move';
  });
  list.addEventListener('drop', (event) => {
    if (!dragged) return;
    event.preventDefault();
    const target = event.target.closest('.submission');
    if (!target || dragged === target) return;
    if (dragged.compareDocumentPosition(target) & Node.DOCUMENT_POSITION_FOLLOWING) target.after(dragged);
    else target.before(dragged);
    updateOrder();
  });
  list.addEventListener('dragend', () => {
    dragged?.classList.remove('dragging');
    dragged = null;
  });
  list.addEventListener('click', (event) => {
    const move = event.target.closest('[data-move]');
    if (!move || move.getAttribute('aria-disabled') === 'true') return;
    const entry = move.closest('.submission');
    if (move.dataset.move === '-1') entry.previousElementSibling.before(entry);
    else entry.nextElementSibling.after(entry);
    move.focus();
    updateOrder();
  });
  for (const controls of list.querySelectorAll('.sort-controls')) controls.hidden = false;
  orderForm.hidden = false;
  updateOrder();
}
