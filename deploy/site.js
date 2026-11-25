'use strict';

const lang = document.documentElement.lang.startsWith('zh') ? 'zh' : 'en';
const topic = document.body.dataset.problem;
const guideUrl = 'https://www.movan.tech/goldbach/' + (topic ? 'problems/' + topic + '/' : '') +
  (lang === 'zh' ? 'join-zh.txt' : 'join.txt');
const claimCommand = 'python tools/goldbach.py claim' + (topic ? ' --problem ' + topic : '');
const repository = 'https://github.com/CGandGameEngineLearner/goldbach-proofs';
const menu = document.querySelector('.menu-toggle');
const navigation = document.getElementById('site-nav');
menu.addEventListener('click', () => {
  menu.setAttribute('aria-expanded', String(navigation.classList.toggle('expanded')));
});
navigation.addEventListener('click', () => {
  navigation.classList.remove('expanded');
  menu.setAttribute('aria-expanded', 'false');
});
const strings = {
  zh: {
    open: '待证', proved: '已通过', accepted: '已通过', rejected: '已拒绝',
    assignments: { working: '已领取', submitted: '已提交', checking: '验证中' },
    run: '查看运行', latestRun: '最近运行', noRun: '暂无', attempt: '运行尝试',
    manifest: '查看证据清单', empty: '没有匹配的引理。', noRecords: '还没有权威验证记录。',
    count: n => '找到 ' + n + ' 条引理。',
    failure: '暂时无法获取实时数据。', published: '查看 GitHub 命题清单', actions: '查看 GitHub Actions',
    copied: '已复制', copyManual: '请复制已选中的提示词。',
    stale: '暂时无法刷新，正在显示上次获取的数据。',
    deskUnavailable: '暂时无法获取社区数据。',
    noActivity: '暂无参与记录。',
    noContributors: '暂无有署名的通过记录。',
    noHourContributors: '最近一小时暂无首次通过的引理。',
    rankingsUnavailable: '暂时无法获取贡献榜。',
    rankingsCount: n => '共 ' + n + ' 位贡献者。',
    rankingsSummary: (people, proofs) => people + ' 位贡献者的 ' + proofs + ' 条引理已通过权威 Lean 验证。',
    rankingPeriods: { hour: '最近一小时', all_time: '累计' },
    justNow: '刚刚',
    participant: '参与者',
    activities: {
      claimed: '领取引理', submitted: '登记提交', checking: '开始验证',
      released: '归还引理', accepted: '验证通过', rejected: '验证拒绝', expired: '任务凭证过期'
    },
    event: '任务状态更新',
    verifiedCount: n => '通过 ' + n + ' 条',
    pullRequest: '查看 PR',
    allPrograms: '全部路线',
    programCount: (verified, published) => verified + ' / ' + published + ' 已通过',
    pageRange: (first, last, total) => '第 ' + first + '–' + last + ' 条，共 ' + total + ' 条',
    file: '证明文件',
    copyLemma: '复制这条引理的参与提示词',
    occupied: '这条引理当前正在处理。',
    alreadyVerified: '这条引理已通过权威验证。',
    lemmaPrompt: id => '读取 ' + guideUrl + '，按指南用 ' + claimCommand + ' ' + id + ' 领取并验证这一条引理。如果无法领取这条引理，请说明原因，不要改领其他题。'
  },
  en: {
    open: 'Open', proved: 'Verified', accepted: 'Accepted', rejected: 'Rejected',
    assignments: { working: 'Claimed', submitted: 'Submitted', checking: 'Checking' },
    run: 'View run', latestRun: 'Latest run', noRun: 'Pending', attempt: 'Attempt',
    manifest: 'View evidence manifest', empty: 'No matching lemmas.', noRecords: 'No authoritative runs have been recorded.',
    count: n => n === 1 ? '1 matching lemma.' : n + ' matching lemmas.',
    failure: 'Live data is temporarily unavailable.', published: 'View statements on GitHub', actions: 'View GitHub Actions',
    copied: 'Copied', copyManual: 'Copy the selected prompt.',
    stale: 'Refresh failed. Showing the last available data.',
    deskUnavailable: 'Community data is temporarily unavailable.',
    noActivity: 'No community activity yet.',
    noContributors: 'No attributed proofs have passed verification yet.',
    noHourContributors: 'No lemmas passed for the first time in the past hour.',
    rankingsUnavailable: 'The leaderboard is temporarily unavailable.',
    rankingsCount: n => n + (n === 1 ? ' contributor.' : ' contributors.'),
    rankingsSummary: (people, proofs) => people + (people === '1' ? ' contributor has ' : ' contributors have ') +
      proofs + (proofs === '1' ? ' proof accepted by Lean.' : ' proofs accepted by Lean.'),
    rankingPeriods: { hour: 'This hour', all_time: 'All time' },
    justNow: 'Just now',
    participant: 'Participant',
    activities: {
      claimed: 'Claimed a lemma', submitted: 'Registered a submission', checking: 'Started verification',
      released: 'Returned a lemma', accepted: 'Proof accepted', rejected: 'Proof rejected', expired: 'Lease expired'
    },
    event: 'Task status changed',
    verifiedCount: n => n === 1 ? '1 accepted' : n + ' accepted',
    pullRequest: 'View PR',
    allPrograms: 'All programs',
    programCount: (verified, published) => verified + ' / ' + published + ' verified',
    pageRange: (first, last, total) => first + '–' + last + ' of ' + total + ' lemmas',
    file: 'Proof file',
    copyLemma: 'Copy this lemma’s join prompt',
    occupied: 'This lemma is currently in progress.',
    alreadyVerified: 'The authoritative verifier has accepted this lemma.',
    lemmaPrompt: id => 'Read ' + guideUrl + ' and follow it to claim and verify exactly ' + id + ' with ' + claimCommand + ' ' + id + '. If that lemma is unavailable, report why and do not choose another.'
  }
}[lang];

function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function anchor(label, href, className) {
  const link = element('a', label, className);
  link.href = href;
  return link;
}

function runLink(run, label) {
  return anchor(label + ' ↗', repository + '/actions/runs/' + run.run_id, 'evidence-link');
}

function verdictTag(label, status) {
  return element('span', label, status ? 'verdict verdict-' + status : 'verdict');
}

const lemmaRows = document.getElementById('lemma-rows');
const lemmaSearch = document.getElementById('lemma-search');
const lemmaState = document.getElementById('lemma-state');
const verificationLog = document.getElementById('verification-log');
const deskNotice = document.getElementById('desk-notice');
const deskActivity = document.getElementById('desk-activity');
const rankingsList = document.getElementById('rankings-list');
const rankingsModes = Array.from(document.querySelectorAll('[data-ranking-mode]'));
const rankingsAll = document.getElementById('rankings-all');
const rankingsDialog = document.getElementById('rankings-dialog');
const rankingsFullList = document.getElementById('rankings-full-list');
const rankingsAnnouncement = document.getElementById('rankings-announcement');
let rankingsData = null;
let rankingsSnapshot = null;
let rankingMode = null;
let agentRankingsData = null;
const locale = document.documentElement.lang;
const eventTime = new Intl.DateTimeFormat(locale, { dateStyle: 'medium', timeStyle: 'short' });
const relativeTime = new Intl.RelativeTimeFormat(locale, { numeric: 'auto' });

const mapNodes = document.getElementById('map-nodes');
const mapContext = document.getElementById('map-context');
const mapReset = document.getElementById('map-reset');
const programButtons = Array.from(document.querySelectorAll('[data-program]'));
const programs = new Map(programButtons.map(button => [button.dataset.program, button]));
const lemmaDialog = document.getElementById('lemma-detail');
const detailContent = document.getElementById('lemma-detail-content');
const pageRange = document.getElementById('lemma-page-range');
const previousPage = document.getElementById('lemma-prev');
const nextPage = document.getElementById('lemma-next');
const pageSelect = document.getElementById('lemma-page');
const pageSize = 24;

let publishedGaps = [];
let assignments = {};
let selectedProgram = '';
let selectedGap = null;
let lemmaPage = 1;
let loading = false;
let lastGaps = null;
let lastResults = null;
let lastDesk = null;

function messageRow(label, link) {
  const row = element('tr');
  const cell = element('td', label, 'empty-state');
  cell.colSpan = 3;
  if (link) cell.append(link);
  row.append(cell);
  return row;
}

function programOf(gap) {
  return programs.has(gap.track) ? gap.track : gap.program || 'foundation';
}

function programName(key) {
  return programs.get(key)?.querySelector('.program-name').textContent ?? '';
}

function assigned(gap) {
  return !gap.proved && Object.hasOwn(strings.assignments, assignments[gap.id]);
}

function gapStatus(gap) {
  if (gap.proved) return { label: strings.proved, kind: 'verified', style: 'accepted' };
  if (assigned(gap)) {
    return { label: strings.assignments[assignments[gap.id]], kind: 'occupied', style: 'in-progress' };
  }
  return { label: strings.open, kind: 'available', style: '' };
}

function canClaim(gap) {
  return !gap.proved && (!assigned(gap) || gap.parallel === true);
}

function renderProgramCounts() {
  const counts = new Map(Array.from(programs.keys(), key => [key, { published: 0, verified: 0 }]));
  for (const gap of publishedGaps) {
    const count = counts.get(programOf(gap));
    if (!count) continue;
    count.published += 1;
    if (gap.proved) count.verified += 1;
  }
  for (const [key, count] of counts) {
    programs.get(key).querySelector('.program-count').textContent = strings.programCount(count.verified, count.published);
  }
}

function chooseProgram(program) {
  selectedProgram = program;
  for (const [key, button] of programs) {
    button.setAttribute('aria-pressed', String(key === program));
  }
  mapContext.textContent = programName(program) || strings.allPrograms;
  mapReset.hidden = !program;
  lemmaPage = 1;
  if (lastGaps !== null) renderLemmas();
}

for (const [key, button] of programs) {
  button.addEventListener('click', () => chooseProgram(selectedProgram === key ? '' : key));
}
mapReset.addEventListener('click', () => {
  programs.get(selectedProgram)?.focus();
  chooseProgram('');
});

function openGap(id) {
  selectedGap = id;
  renderGapDetail();
  if (!lemmaDialog.open) lemmaDialog.showModal();
  detailContent.scrollTop = 0;
}

document.getElementById('roadmap')?.addEventListener('click', event => {
    const link = event.target.closest('a[data-roadmap-task]');
    if (!link || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    if (publishedGaps.some(gap => gap.id === link.dataset.roadmapTask)) {
      event.preventDefault();
      openGap(link.dataset.roadmapTask);
    }
});

function renderGapDetail() {
  const gap = publishedGaps.find(entry => entry.id === selectedGap);
  if (!gap) return;
  const status = gapStatus(gap);
  const identity = element('div', undefined, 'detail-identity');
  identity.append(element('code', gap.id), verdictTag(status.label, status.style));
  const role = {
    endpoint: lang === 'zh' ? '与强哥德巴赫猜想等价的总目标' : 'Final target equivalent to strong Goldbach',
    target: lang === 'zh' ? '待突破的解析估计' : 'Open analytic target',
    conditional: lang === 'zh' ? '需使用命题中所列假设' : 'Conditional on the stated hypotheses'
  }[gap.role];
  const challenge = gap.challenge_only && (lang === 'zh' ? '核心开放难题 · 仅按 ID 主动挑战' : 'Open research challenge · claim explicitly by ID');
  const context = [programName(programOf(gap)), role, challenge].filter(Boolean).join(' · ');
  detailContent.replaceChildren(
    identity,
    element('h3', gap.plain_statement[lang]),
    element('p', context, 'detail-context'),
    element('pre', gap.statement, 'detail-statement')
  );

  if (gap.brief?.[lang]) detailContent.append(element('p', gap.brief[lang], 'detail-context'));
  if (gap.source) detailContent.append(anchor(lang === 'zh' ? '阅读来源 ↗' : 'Read the source ↗', gap.source, 'evidence-link'));
  if (!gap.proved && gap.parallel) detailContent.append(element('p',
    lang === 'zh' ? '此问题开放给多个参与者独立试证。' : 'This problem accepts independent proof attempts in parallel.', 'detail-context'));
  if (gap.file) {
    const file = element('p', undefined, 'detail-file');
    file.append(element('strong', strings.file), element('code', gap.file));
    detailContent.append(file);
  }
  if (gap.latest) {
    detailContent.append(runLink(gap.latest, strings.latestRun));
  }
  if (!canClaim(gap)) {
    detailContent.append(element('p', gap.proved ? strings.alreadyVerified : strings.occupied, 'detail-context'));
    return;
  }
  const join = element('div', undefined, 'detail-join');
  const copy = element('button', strings.copyLemma, 'button button-primary');
  copy.type = 'button';
  const prompt = element('p', strings.lemmaPrompt(gap.id), 'join-prompt');
  const announcement = element('span', undefined, 'join-feedback');
  announcement.setAttribute('role', 'status');
  bindPromptCopy(copy, prompt, announcement);
  join.append(copy, prompt, announcement);
  detailContent.append(join);
}

lemmaDialog.addEventListener('close', () => { selectedGap = null; });

function lemmaRow(gap) {
  const row = element('tr');
  const claim = element('td');
  const button = element('button', gap.plain_statement[lang], 'statement-link');
  button.type = 'button';
  button.addEventListener('click', () => openGap(gap.id));
  claim.append(element('code', gap.id, 'statement-id'), button);
  const context = programName(programOf(gap));
  if (context) claim.append(element('span', context, 'row-context'));

  const statusCell = element('td');
  const status = gapStatus(gap);
  statusCell.append(verdictTag(status.label, status.style));
  const evidence = element('td');
  if (gap.latest) {
    evidence.append(runLink(gap.latest, strings.latestRun));
  } else {
    evidence.append(element('span', strings.noRun));
  }
  row.append(claim, statusCell, evidence);
  return row;
}

function mapNode(gap) {
  const status = gapStatus(gap);
  const button = element('button', undefined, 'map-node');
  const dot = element('span', undefined, 'map-dot ' + status.kind);
  dot.setAttribute('aria-hidden', 'true');
  button.type = 'button';
  button.setAttribute('aria-label', gap.id + ' · ' + status.label);
  button.title = gap.plain_statement[lang];
  button.append(dot, element('code', gap.id.replace('L-' + (topic || 'goldbach') + '-', '')));
  button.addEventListener('click', () => openGap(gap.id));
  return button;
}

const graph = document.getElementById('network-map');
const palette = { available: '#aebcaf', occupied: '#f2be63', verified: '#9cdaa2' };
const programPalette = { foundation: '#a0c6a1', grh: '#ebc883', correlation: '#9ab9d7', exceptions: '#c4acd7' };
let graphGaps = [];
let graphTargets = [];
function drawNetwork() {
  const w = graph.clientWidth;
  const h = graph.clientHeight;
  const ctx = graph.getContext('2d');
  if (!ctx || !w || !h) return;
  const scale = Math.min(window.devicePixelRatio || 1, 2);
  graph.width = Math.round(w * scale);
  graph.height = Math.round(h * scale);
  ctx.scale(scale, scale);
  graphTargets = [];
  const center = { x: w / 2, y: h / 2 };
  function edge(a, b, color) {
    ctx.strokeStyle = color;
    ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
  }
  function dot(p, radius, color) {
    ctx.fillStyle = color; ctx.beginPath(); ctx.arc(p.x, p.y, radius, 0, 2 * Math.PI); ctx.fill();
  }
  function caption(p, text, color) {
    ctx.font = w < 460 ? '550 11px system-ui, sans-serif' : '550 13px system-ui, sans-serif';
    ctx.textAlign = 'center';
    const width = Math.min(ctx.measureText(text).width, w * (selectedProgram ? .85 : .44));
    ctx.beginPath();
    if (ctx.roundRect) ctx.roundRect(p.x - width / 2 - 8, p.y - 12, width + 16, 24, 4);
    else ctx.rect(p.x - width / 2 - 8, p.y - 12, width + 16, 24);
    ctx.fillStyle = '#192b23';
    ctx.fill();
    ctx.strokeStyle = color + '90';
    ctx.stroke();
    ctx.fillStyle = color;
    ctx.fillText(text, p.x, p.y + 4, width);
  }
  const keys = selectedProgram ? [selectedProgram] : [...programs.keys()];
  keys.forEach((key, index) => {
    const gaps = graphGaps.filter(gap => programOf(gap) === key);
    if (!gaps.length) return;
    const hub = selectedProgram ? center : {
      x: w * (index % 2 ? 0.75 : 0.25), y: h * (Math.floor(index / 2) + 0.5) / Math.ceil(keys.length / 2)
    };
    const tint = programPalette[key] || ['#8ed9ca', '#ecac93'][index % 2];
    if (!selectedProgram) edge(center, hub, tint + '66');
    const radiusX = w * (selectedProgram ? .44 : .19);
    const radiusY = h * (selectedProgram ? .43 : .40 / Math.ceil(keys.length / 2));
    gaps.forEach((gap, i) => {
      const angle = i * Math.PI * (3 - Math.sqrt(5));
      const radius = Math.sqrt((i + 1) / gaps.length);
      const p = { x: hub.x + radius * radiusX * Math.cos(angle),
        y: hub.y + radius * radiusY * Math.sin(angle) };
      edge(hub, p, tint + '70');
      const { kind } = gapStatus(gap);
      dot(p, selectedProgram ? 7 : 6, palette[kind] + '26');
      dot(p, selectedProgram ? 4.25 : 3.5, palette[kind]);
      graphTargets.push({ ...p, gap, radius: 10 });
    });
    caption(hub, programName(key), tint);
    graphTargets.push({ ...hub, program: key, radius: 15 });
  });
  if (!selectedProgram || !graphGaps.length) {
    caption(center, graphGaps.length ? (topic ? (lang === 'zh' ? '研究路线' : 'Research') : lang === 'zh' ? '强哥德巴赫' : 'Binary Goldbach') : strings.empty, '#f1ddb1');
  }
}
function graphTarget(event) {
  const bounds = graph.getBoundingClientRect();
  const x = event.clientX - bounds.left;
  const y = event.clientY - bounds.top;
  let nearest, distance = Infinity;
  for (const target of graphTargets) {
    const d = Math.hypot(x - target.x, y - target.y);
    if (d <= target.radius && d < distance) { nearest = target; distance = d; }
  }
  return nearest;
}
graph.addEventListener('pointermove', event => {
  const target = graphTarget(event);
  graph.style.cursor = target ? 'pointer' : 'default';
  graph.title = target?.gap?.plain_statement[lang] || (target ? programName(target.program) : '');
});
graph.addEventListener('click', event => {
  const target = graphTarget(event);
  if (target?.gap) openGap(target.gap.id);
  else if (target) chooseProgram(selectedProgram ? '' : target.program);
});
new ResizeObserver(drawNetwork).observe(graph);

function renderLemmas() {
  const query = lemmaSearch.value.trim().toLocaleLowerCase();
  const selection = lemmaState.value;
  const visibleGaps = publishedGaps.filter(gap => {
    if (selectedProgram && programOf(gap) !== selectedProgram) return false;
    if (selection === 'proved' && !gap.proved) return false;
    if (selection === 'open' && gap.proved) return false;
    if (selection === 'progress' && !assigned(gap)) return false;
    if (selection === 'available' && !canClaim(gap)) return false;
    if (!query) return true;
    const program = programOf(gap);
    const content = [
      gap.id, gap.statement, gap.plain_statement.zh, gap.plain_statement.en,
      program, programName(program), gap.brief?.[lang] || ''
    ];
    return content.some(text => text.toLocaleLowerCase().includes(query));
  });
  graphGaps = visibleGaps;
  drawNetwork();
  const maxPage = Math.max(1, Math.ceil(visibleGaps.length / pageSize));
  lemmaPage = Math.min(lemmaPage, maxPage);
  const offset = (lemmaPage - 1) * pageSize;
  const current = visibleGaps.slice(offset, offset + pageSize);
  mapNodes.replaceChildren(...current.map(mapNode));
  lemmaRows.replaceChildren(...(current.length ? current.map(lemmaRow) : [messageRow(strings.empty)]));
  pageRange.textContent = current.length ? strings.pageRange(offset + 1, offset + current.length, visibleGaps.length) : strings.empty;
  previousPage.disabled = lemmaPage === 1;
  nextPage.disabled = lemmaPage === maxPage;
  pageSelect.disabled = maxPage === 1;
  if (pageSelect.options.length !== maxPage) {
    pageSelect.replaceChildren(...Array.from({ length: maxPage }, (_, index) => new Option(index + 1, index + 1)));
  }
  pageSelect.value = String(lemmaPage);
}

function setPage(page) {
  lemmaPage = page;
  renderLemmas();
}

previousPage.addEventListener('click', () => setPage(lemmaPage - 1));
nextPage.addEventListener('click', () => setPage(lemmaPage + 1));
pageSelect.addEventListener('change', () => setPage(Number(pageSelect.value)));

function renderLogEntry(run) {
  const article = element('article');
  article.dataset.run = run.run_id + '/' + run.run_attempt;
  const row = element('div', undefined, 'log-entry');
  const judgement = run.verdict === 'ACCEPTED' ? 'accepted' : 'rejected';
  const label = element('div');
  label.append(
    element('code', run.lemma_id, 'log-id'),
    element('span', strings.attempt + ' ' + run.run_attempt + ' · #' + run.run_id, 'log-note')
  );
  row.append(label, verdictTag(strings[judgement], judgement), runLink(run, strings.run));
  article.append(row);
  if (run.agent) {
    const a = run.agent;
    const model = agentName(a.model), harness = agentName(a.harness);
    const version = a.harness_version && a.harness_version !== 'unknown' ? ' ' + a.harness_version : '';
    article.append(element('p', (lang === 'zh' ? '模型：' : 'Model: ') + model +
      ' · Harness: ' + harness + version + ' · ' +
      (a.source === 'self_reported' ? (lang === 'zh' ? '提交者自报' : 'Self-reported') :
        (lang === 'zh' ? '未记录' : 'Unrecorded')), 'log-note agent-attribution'));
  }
  if (run.manifest) {
    const details = element('details', undefined, 'manifest');
    details.append(
      element('summary', strings.manifest),
      element('pre', JSON.stringify(run.manifest, null, 2))
    );
    article.append(details);
  }
  return article;
}

function renderActivity(event) {
  const item = element('li', undefined, 'activity-item');
  const details = element('div', undefined, 'activity-details');
  const label = Object.hasOwn(strings.activities, event.kind) ? strings.activities[event.kind] : strings.event;
  const byline = element('div', undefined, 'activity-byline');
  byline.append(element('span', event.handle || strings.participant), element('code', event.lemma_id));
  details.append(element('strong', label), byline);

  const links = element('div', undefined, 'activity-links');
  const date = new Date(typeof event.at === 'number' ? event.at * 1000 : event.at);
  if (Number.isFinite(date.getTime())) {
    const timestamp = element('time', eventTime.format(date));
    timestamp.dateTime = date.toISOString();
    links.append(timestamp);
  }
  if (Number.isSafeInteger(event.run_id) && event.run_id > 0) {
    links.append(runLink(event, strings.run));
  } else if (Number.isSafeInteger(event.pr) && event.pr > 0) {
    links.append(anchor(strings.pullRequest + ' ↗', repository + '/pull/' + event.pr, 'evidence-link'));
  }
  item.append(details, links);
  return item;
}

function rankingTimeText(acceptedAt) {
  const age = Math.max(0, Math.floor(Date.now() / 1000 - acceptedAt));
  if (age < 60) return strings.justNow;
  if (age < 3600) return relativeTime.format(-Math.floor(age / 60), 'minute');
  if (age < 86400) return relativeTime.format(-Math.floor(age / 3600), 'hour');
  return relativeTime.format(-Math.floor(age / 86400), 'day');
}

function zhihuUrl(value, kind) {
  if (typeof value !== 'string' || !value) return null;
  let url;
  try {
    url = new URL(value);
  } catch {
    return null;
  }
  if (url.protocol !== 'https:' || url.username || url.password || url.port) return null;
  if (kind === 'avatar') {
    return url.hostname.endsWith('.zhimg.com') ? url.href : null;
  }
  return url.hostname === 'www.zhihu.com' && /^\/people\/[^/]+\/?$/.test(url.pathname)
    ? url.href : null;
}

function renderRankingRow(contributor, index, mode) {
  const item = element('li', undefined, 'ranking-row');
  const rank = element('span', index + 1, 'ranking-position');
  const zhihu = contributor.zhihu;
  const name = typeof zhihu?.name === 'string' ? zhihu.name.trim() : '';
  const avatarUrl = name && zhihuUrl(zhihu.avatar_url, 'avatar');
  const profileUrl = name && zhihuUrl(zhihu.profile_url, 'profile');
  const github = 'https://github.com/' + encodeURIComponent(contributor.handle);
  const githubAvatar = github + '.png?size=64';
  const avatar = element('span', contributor.handle[0].toUpperCase(), 'ranking-avatar');
  avatar.setAttribute('aria-hidden', 'true');
  const photograph = document.createElement('img');
  photograph.alt = '';
  photograph.width = 38;
  photograph.height = 38;
  photograph.loading = 'lazy';
  photograph.referrerPolicy = 'no-referrer';
  photograph.addEventListener('error', () => {
    if (photograph.src === githubAvatar) photograph.remove();
    else photograph.src = githubAvatar;
  });
  photograph.src = avatarUrl || githubAvatar;
  avatar.append(photograph);

  const identity = element('div', undefined, 'ranking-identity');
  if (name) {
    const label = (lang === 'zh' ? '知乎 · ' : 'Zhihu · ') + name;
    identity.append(profileUrl ? anchor(label, profileUrl, 'ranking-name') : element('span', label, 'ranking-name'));
    identity.append(anchor('GitHub · @' + contributor.handle, github, 'ranking-github'));
  } else {
    identity.append(anchor('@' + contributor.handle, github, 'ranking-name'));
  }
  if (Number.isSafeInteger(contributor.latest_accepted_at)) {
    const acceptedAt = contributor.latest_accepted_at;
    const date = new Date(acceptedAt * 1000);
    const time = element('time', rankingTimeText(acceptedAt), 'ranking-time');
    time.dataset.rankTime = String(acceptedAt);
    time.dateTime = date.toISOString();
    time.title = eventTime.format(date);
    identity.append(time);
  }
  const score = element('div', undefined, 'ranking-result');
  const figure = element('span', '+' + contributor.accepted.toLocaleString(locale), 'ranking-score');
  figure.setAttribute('aria-hidden', 'true');
  score.append(figure, element('span', strings.verifiedCount(contributor.accepted), 'sr-only'),
    element('span', strings.rankingPeriods[mode], 'ranking-period'));
  item.append(rank, avatar, identity, score);
  return item;
}

function updateRankingTimes() {
  for (const date of document.querySelectorAll('[data-rank-time]')) {
    date.textContent = rankingTimeText(Number(date.dataset.rankTime));
  }
}

function agentName(name) {
  if (!name || name === 'unknown') return lang === 'zh' ? '未记录／未知' : 'Unknown / unrecorded';
  const tools = {codex: 'Codex', 'claude-code': 'Claude Code', cursor: 'Cursor', 'gemini-cli': 'Gemini CLI', opencode: 'OpenCode', other: lang === 'zh' ? '其他工具' : 'Other tools'};
  return tools[name] || name;
}

const agentBrandRules = [
  [/(?:^|[ /:_-])(?:codex)(?=$|[ /:_.0-9-])/, 22],
  [/(?:^|[ /:_-])(?:claude-code)(?=$|[ /:_.0-9-])/, 23],
  [/(?:^|[ /:_-])(?:gemini-cli)(?=$|[ /:_.0-9-])/, 25],
  [/(?:^|[ /:_-])(?:cursor)(?=$|[ /:_.0-9-])/, 24],
  [/(?:^|[ /:_-])(?:opencode)(?=$|[ /:_.0-9-])/, 26],
  [/(?:^|[ /:_-])(?:openai|gpt|chatgpt|o[134](?:-|$))(?=$|[ /:_.0-9-])/, 0],
  [/(?:^|[ /:_-])(?:anthropic|claude)(?=$|[ /:_.0-9-])/, 1],
  [/(?:^|[ /:_-])(?:gemini)(?=$|[ /:_.0-9-])/, 2],
  [/(?:^|[ /:_-])(?:deepseek)(?=$|[ /:_.0-9-])/, 3],
  [/(?:^|[ /:_-])(?:qwen|qwq|qvq|tongyi)(?=$|[ /:_.0-9-])/, 4],
  [/(?:^|[ /:_-])(?:xai|x-ai|grok)(?=$|[ /:_.0-9-])/, 5],
  [/(?:^|[ /:_-])(?:meta|llama)(?=$|[ /:_.0-9-])/, 6],
  [/(?:^|[ /:_-])(?:mistral|mixtral|codestral|devstral|magistral)(?=$|[ /:_.0-9-])/, 7],
  [/(?:^|[ /:_-])(?:kimi)(?=$|[ /:_.0-9-])/, 8],
  [/(?:^|[ /:_-])(?:moonshot)(?=$|[ /:_.0-9-])/, 33],
  [/(?:^|[ /:_-])(?:zhipu|zai|z-ai|glm|chatglm)(?=$|[ /:_.0-9-])/, 9],
  [/(?:^|[ /:_-])(?:doubao|seed|bytedance)(?=$|[ /:_.0-9-])/, 10],
  [/(?:^|[ /:_-])(?:baidu|ernie)(?=$|[ /:_.0-9-])/, 11],
  [/(?:^|[ /:_-])(?:minimax)(?=$|[ /:_.0-9-])/, 12],
  [/(?:^|[ /:_-])(?:yi(?:-|$)|01-ai)(?=$|[ /:_.0-9-])/, 13],
  [/(?:^|[ /:_-])(?:cohere|command)(?=$|[ /:_.0-9-])/, 14],
  [/(?:^|[ /:_-])(?:ai21|jamba)(?=$|[ /:_.0-9-])/, 15],
  [/(?:^|[ /:_-])(?:nvidia|nemotron)(?=$|[ /:_.0-9-])/, 16],
  [/(?:^|[ /:_-])(?:microsoft|phi)(?=$|[ /:_.0-9-])/, 17],
  [/(?:^|[ /:_-])(?:hunyuan)(?=$|[ /:_.0-9-])/, 18],
  [/(?:^|[ /:_-])(?:stepfun|step(?:-|$))(?=$|[ /:_.0-9-])/, 19],
  [/(?:^|[ /:_-])(?:gemma)(?=$|[ /:_.0-9-])/, 20],
  [/(?:^|[ /:_-])(?:google|palm)(?=$|[ /:_.0-9-])/, 21],
  [/(?:^|[ /:_-])(?:perplexity|sonar)(?=$|[ /:_.0-9-])/, 27],
  [/(?:^|[ /:_-])(?:alibaba)(?=$|[ /:_.0-9-])/, 28],
  [/(?:^|[ /:_-])(?:tencent)(?=$|[ /:_.0-9-])/, 29],
  [/(?:^|[ /:_-])(?:ibm|granite)(?=$|[ /:_.0-9-])/, 30],
  [/(?:^|[ /:_-])(?:huggingface|smollm)(?=$|[ /:_.0-9-])/, 31],
];

function agentBrandIcon(name) {
  const match = agentBrandRules.find(([pattern]) => pattern.test(name.toLowerCase()));
  const icon = element('span', match ? '' : name.slice(0, 1).toUpperCase(), 'agent-brand-icon');
  icon.setAttribute('aria-hidden', 'true');
  if (match) {
    icon.classList.add('has-brand');
    icon.style.backgroundPosition = '-' + (match[1] * 32) + 'px 0';
  }
  return icon;
}

function renderAgentRankingRow(entry, index) {
  const item = element('li', undefined, 'ranking-row agent-ranking-row');
  const name = element('strong', undefined, 'ranking-name agent-brand-name');
  name.append(agentBrandIcon(entry.name), element('span', agentName(entry.name)));
  item.append(element('span', index + 1, 'ranking-position'), name);
  const result = element('div', undefined, 'ranking-result');
  result.append(element('span', '+' + entry.accepted.toLocaleString(locale), 'ranking-score'),
    element('span', strings.rankingPeriods.all_time, 'ranking-period'));
  item.append(result);
  return item;
}

function renderAgentColumns(container, limit = Infinity) {
  container.replaceChildren(...['models', 'harnesses'].map(dimension => {
    const column = element('section', undefined, 'agent-ranking-column');
    const title = dimension === 'models' ? (lang === 'zh' ? '模型' : 'Models') : (lang === 'zh' ? 'Harness 工具' : 'Harness tools');
    const list = element('ol', undefined, 'ranking-list');
    list.setAttribute('aria-label', title);
    fillRankings(list, (agentRankingsData?.[dimension] || []).slice(0, limit), 'agents');
    column.append(element('h3', title), list);
    return column;
  }));
}

function renderFullRankings() {
  const agents = rankingMode === 'agents';
  const columns = document.getElementById('agent-rankings-full');
  columns.hidden = !agents;
  rankingsFullList.hidden = agents;
  if (agents) renderAgentColumns(columns);
  else fillRankings(rankingsFullList, rankingsData.all_time, 'all_time');
}

function fillRankings(list, data, mode) {
  const empty = mode === 'agents'
    ? (agentRankingsData ? (lang === 'zh' ? '暂无通过验证的记录。' : 'No verified contributions yet.') : strings.rankingsUnavailable)
    : mode === 'hour' ? strings.noHourContributors : strings.noContributors;
  list.replaceChildren(...(data.length
    ? data.map((entry, index) => mode === 'agents' ? renderAgentRankingRow(entry, index) : renderRankingRow(entry, index, mode))
    : [element('li', empty, 'ranking-empty')]));
}

function renderRankingMode() {
  if (!rankingsData) return;
  const agents = rankingMode === 'agents';
  const rows = agents ? (agentRankingsData?.models || []) : rankingsData[rankingMode];
  const columns = document.getElementById('agent-ranking-columns');
  columns.hidden = !agents;
  rankingsList.hidden = agents;
  if (agents) renderAgentColumns(columns, 6);
  document.getElementById('agent-ranking-controls').hidden = !agents;
  document.querySelector('.ranking-candidate').hidden = agents;
  rankingsAll.disabled = agents && !agentRankingsData;
  rankingsAll.textContent = agents ? (lang === 'zh' ? '查看完整榜单 ↗' : 'See full leaderboard ↗') :
    (lang === 'zh' ? '查看全部贡献者 ↗' : 'See all contributors ↗');
  document.getElementById('rankings-dialog-title').textContent = agents
    ? (lang === 'zh' ? '模型与 Harness 贡献榜' : 'Model and harness contributions')
    : (lang === 'zh' ? '全部已核验贡献者' : 'All verified contributors');
  document.getElementById('rankings-summary').textContent = agents
    ? (lang === 'zh' ? '按本研究台累计首次通过的引理数排列。' : 'Ranked by all-time first accepted lemmas on this research desk.')
    : strings.rankingsSummary(rankingsData.contributors.toLocaleString(locale), rankingsData.proofs.toLocaleString(locale));
  fillRankings(rankingsList, rows.slice(0, 6), rankingMode);
  document.getElementById('ranking-next-place').textContent = String(rows.length + 1);
  rankingsAnnouncement.textContent = agents ? (lang === 'zh' ? '共 ' + rows.length + ' 项。' : rows.length + ' entries.') : strings.rankingsCount(rows.length);
  if (rankingsDialog.open) renderFullRankings();
}

function selectRankingMode(mode) {
  rankingMode = mode;
  for (const button of rankingsModes) button.setAttribute('aria-pressed', String(button.dataset.rankingMode === mode));
  renderRankingMode();
}

function renderRankings(rankings, agentRankings) {
  if (!rankings) {
    if (!rankingsData) rankingsList.replaceChildren(element('li', strings.rankingsUnavailable, 'ranking-empty'));
    return;
  }
  const snapshot = JSON.stringify({rankings, agentRankings});
  if (rankingsSnapshot === snapshot) {
    updateRankingTimes();
    return;
  }
  rankingsData = rankings;
  agentRankingsData = agentRankings || null;
  rankingsSnapshot = snapshot;
  rankingsAll.disabled = false;
  document.getElementById('rankings-summary').textContent = strings.rankingsSummary(
    rankings.contributors.toLocaleString(locale), rankings.proofs.toLocaleString(locale)
  );
  selectRankingMode(rankingMode ?? (rankings.hour.length ? 'hour' : 'all_time'));

}

for (const button of rankingsModes) {
  button.addEventListener('click', () => selectRankingMode(button.dataset.rankingMode));
}
rankingsAll.addEventListener('click', () => {
  renderFullRankings();
  rankingsDialog.showModal();
});

function showDeskNotice(message) {
  if (deskNotice.textContent !== message) deskNotice.textContent = message;
  deskNotice.hidden = !message;
}

function renderDesk(desk) {
  renderRankings(desk?.rankings, desk?.agent_rankings);
  if (!desk) {
    showDeskNotice(lastDesk === null ? strings.deskUnavailable : strings.stale);
    if (lastDesk === null) {
      deskActivity.replaceChildren();
    }
    return;
  }
  showDeskNotice('');
  const snapshot = JSON.stringify(desk);
  if (lastDesk === snapshot) return;
  lastDesk = snapshot;
  document.getElementById('desk-active').textContent = desk.active.toLocaleString(locale);
  document.getElementById('live-hero').textContent = desk.active.toLocaleString(locale);
  document.getElementById('hero-sessions').textContent = desk.sessions.toLocaleString(locale);
  const frontier = document.getElementById('frontier-events');
  frontier.replaceChildren(...desk.activities.slice(0, 2).map(activity => {
    const item = element('div', undefined, 'frontier-entry');
    item.append(element('small', eventTime.format(new Date(activity.at * 1000))),
      element('strong', strings.activities[activity.kind] || strings.event),
      element('code', activity.lemma_id));
    return item;
  }));
  if (!desk.activities.length) frontier.textContent = strings.noActivity;
  document.getElementById('desk-sessions').textContent = desk.sessions.toLocaleString(locale);
  deskActivity.replaceChildren(...(desk.activities.length
    ? desk.activities.map(renderActivity) : [element('li', strings.noActivity, 'empty-state')]));
}

function renderResults(results) {
  const snapshot = JSON.stringify(results);
  if (lastResults === snapshot) return;
  lastResults = snapshot;
  const expanded = new Set(Array.from(
    verificationLog.querySelectorAll('details[open]'), details => details.parentElement.dataset.run
  ));
  const entries = results.map(run => {
    const entry = renderLogEntry(run);
    if (expanded.has(entry.dataset.run)) {
      const manifest = entry.querySelector('details');
      if (manifest) manifest.open = true;
    }
    return entry;
  });
  verificationLog.replaceChildren(...(entries.length ? entries : [element('p', strings.noRecords, 'empty-state')]));
}

lemmaSearch.addEventListener('input', () => setPage(1));
lemmaState.addEventListener('change', () => setPage(1));

document.addEventListener('keydown', event => {
  if (event.key !== '/' || event.altKey || event.ctrlKey || event.metaKey ||
      lemmaDialog.open || lemmaSearch.disabled || event.target.closest('input, textarea, select, [contenteditable]')) return;
  event.preventDefault();
  lemmaSearch.focus();
});

const exponentPanel = document.getElementById('lpf-record');
const researchNews = document.getElementById('lpf-news');
if (researchNews && typeof researchNews.showModal === 'function') {
  const opener = document.getElementById('lpf-news-open');
  const seenKey = 'quadratic-primes.news.coe-2026-s41cw';
  opener.addEventListener('click', event => {
    event.preventDefault();
    researchNews.showModal();
  });
  researchNews.addEventListener('close', () => {
    try { localStorage.setItem(seenKey, '1'); } catch {}
    opener.focus({preventScroll: true});
  });
  let seen = false;
  try { seen = localStorage.getItem(seenKey) === '1'; } catch {}
  if (!seen) researchNews.showModal();
}

function renderExponent(record) {
  if (!exponentPanel) return;
  const current = document.getElementById('lpf-current');
  const notice = document.getElementById('lpf-notice');
  if (!record?.current) {
    notice.textContent = current.textContent === '—' ? strings.failure : strings.stale;
    return;
  }
  const zh = lang === 'zh';
  current.textContent = record.current.exponent;
  document.getElementById('lpf-target').textContent = record.target;
  document.getElementById('lpf-kind').textContent = record.current.kind === 'external_certificate'
    ? (zh ? '外部有限证书参数 · 无条件解析转移待核验' : 'External finite certificate · unconditional analytic transfer pending')
    : (zh ? '本站已核验的无条件大素因子界' : 'Unconditional large-prime-factor bound verified here');
  const verified = document.getElementById('lpf-verified');
  if (record.verified) {
    const label = (zh ? '本站 Lean 已通过 · α = ' : 'Site Lean proof · α = ') + record.verified.exponent;
    verified.replaceChildren(anchor(label + ' ↗', record.verified.source_url));
  } else {
    verified.textContent = zh ? '本站暂未通过无条件指数证明。' : 'No unconditional exponent proof has passed here yet.';
  }
  notice.textContent = '';
}

async function loadStatus() {
  if (loading || document.hidden) return;
  loading = true;
  const request = new AbortController();
  const timeout = window.setTimeout(() => request.abort(), 30000);
  try {
    const response = await fetch('api/status?view=web-gzip', {
      headers: { Accept: 'application/json' },
      signal: request.signal,
    });
    if (!response.ok) throw new Error('Status request failed');
    const { gaps, counts, results, desk, lpf_record, catalogue_revision } = await response.json();
    const pageRevision = document.querySelector('meta[name="catalogue-revision"]')?.content;
    if (pageRevision && catalogue_revision && pageRevision !== catalogue_revision) {
      window.location.reload();
      return;
    }
    renderExponent(lpf_record);
    assignments = desk?.assignments ?? assignments;
    document.getElementById('hero-available').textContent = gaps.filter(canClaim).length;
    const latest = results[0];
    document.getElementById('news-verdict').textContent = latest
      ? latest.lemma_id + ' · ' + (latest.verdict === 'ACCEPTED' ? strings.accepted : strings.rejected)
      : strings.noRecords;
    const gapsSnapshot = JSON.stringify([gaps, assignments]);
    if (lastGaps !== gapsSnapshot) {
      publishedGaps = gaps;
      renderProgramCounts();
      renderLemmas();
      if (lemmaDialog.open) renderGapDetail();
      if (lastGaps === null) {
        const requested = new URLSearchParams(window.location.search).get('lemma');
        if (requested && gaps.some(gap => gap.id === requested)) openGap(requested);
      }
      lastGaps = gapsSnapshot;
    }
    lemmaSearch.disabled = false;
    lemmaState.disabled = false;
    for (const name of ['accepted', 'open', 'published', 'attempts']) {
      document.getElementById('count-' + name).textContent = counts[name].toLocaleString(locale);
    }
    const proofProgress = document.getElementById('proof-progress');
    if (proofProgress) {
      proofProgress.max = Math.max(1, counts.published);
      proofProgress.value = counts.accepted;
      document.getElementById('proof-progress-caption').textContent =
        counts.accepted.toLocaleString(locale) + ' / ' + counts.published.toLocaleString(locale);
    }
    renderResults(results);
    renderDesk(desk);
  } catch {
    renderExponent(null);
    if (lastGaps === null) {
      lemmaRows.replaceChildren(messageRow(strings.failure, anchor(strings.published, repository + '/blob/main/research/' + (topic ? 'problems.json' : 'gaps.json'))));
      lemmaSearch.disabled = true;
      lemmaState.disabled = true;
    }
    if (lastResults === null) {
      const error = element('p', strings.failure, 'empty-state');
      error.append(anchor(strings.actions, repository + '/actions'));
      verificationLog.replaceChildren(error);
    }
    renderDesk(null);
  } finally {
    window.clearTimeout(timeout);
    loading = false;
  }
}

function bindPromptCopy(button, prompt, announcement, manualMessage = strings.copyManual) {
  const label = button.textContent;
  let reset;
  button.addEventListener('click', async () => {
    try {
      await navigator.clipboard.writeText(prompt.textContent);
      button.textContent = strings.copied;
      announcement.textContent = strings.copied;
      window.clearTimeout(reset);
      reset = window.setTimeout(() => {
        button.textContent = label;
        announcement.textContent = '';
      }, 1900);
    } catch {
      const disclosure = prompt.closest('details');
      if (disclosure) disclosure.open = true;
      const range = document.createRange();
      range.selectNodeContents(prompt);
      const selection = window.getSelection();
      selection.removeAllRanges();
      selection.addRange(range);
      announcement.textContent = manualMessage;
    }
  });
}

bindPromptCopy(
  document.getElementById('copy-prompt'),
  document.getElementById('agent-prompt'),
  document.getElementById('copy-announcement')
);

const rankingsPrompt = document.getElementById('rankings-prompt');
rankingsPrompt.textContent = document.getElementById('agent-prompt').textContent;
bindPromptCopy(
  document.getElementById('copy-rankings'),
  rankingsPrompt,
  document.getElementById('rankings-copy-announcement')
);

const participation = document.getElementById('participation');
if (participation) {
  const prompt = document.getElementById('participation-prompt');
  prompt.textContent = document.getElementById('agent-prompt').textContent;
  bindPromptCopy(
    document.getElementById('copy-participation-prompt'),
    prompt,
    document.getElementById('participation-copy-announcement')
  );
  bindPromptCopy(
    document.getElementById('copy-github-auth'),
    document.getElementById('github-auth-command'),
    document.getElementById('github-auth-announcement'),
    '请复制已选中的命令。'
  );

  const source = new URLSearchParams(window.location.search).get('from');
  const referrerHost = document.referrer ? new URL(document.referrer).hostname : '';
  if (source === 'zhihu' || referrerHost === 'zhihu.com' || referrerHost.endsWith('.zhihu.com')) {
    participation.open = true;
  }
  const openParticipationAnchor = () => {
    if (window.location.hash === '#participation') {
      participation.open = true;
      participation.scrollIntoView();
    }
  };
  openParticipationAnchor();
  window.addEventListener('hashchange', openParticipationAnchor);
}

loadStatus();
window.setInterval(loadStatus, exponentPanel ? 15000 : 45000);
document.addEventListener('visibilitychange', loadStatus);
