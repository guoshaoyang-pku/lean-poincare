import { mkdir, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";

const outputDirectory = fileURLToPath(new URL("../public/figures/", import.meta.url));

const WIDTH = 420;
const HEIGHT = 300;
const CENTER_X = WIDTH / 2;
const CENTER_Y = HEIGHT / 2;
const SCALE = 112;
const BLUE = "#315da8";
const LIGHT_BLUE = "#8eafe0";
const GREEN = "#4e8a70";
const LIGHT_GREEN = "#a9cdbb";
const RED = "#df5d55";

function fourLobeRadius(theta) {
  const axis = theta - Math.PI / 4;
  const lobe = Math.abs(Math.cos(2 * axis)) ** 2.4;
  return 0.48 + 0.62 * lobe;
}

function pointOnFourArmSurface(theta, latitude) {
  const planarRadius = fourLobeRadius(theta) * Math.cos(latitude);
  const coreBias = 0.82 + 0.18 * Math.abs(Math.cos(2 * (theta - Math.PI / 4)));
  return {
    x: planarRadius * Math.cos(theta),
    y: planarRadius * Math.sin(theta),
    z: 0.58 * coreBias * Math.sin(latitude),
  };
}

function rotatePoint(point) {
  const rotateX = -0.18;
  const rotateY = 0.24;
  const cosX = Math.cos(rotateX);
  const sinX = Math.sin(rotateX);
  const cosY = Math.cos(rotateY);
  const sinY = Math.sin(rotateY);

  const y1 = point.y * cosX - point.z * sinX;
  const z1 = point.y * sinX + point.z * cosX;
  return {
    x: point.x * cosY + z1 * sinY,
    y: y1,
    z: -point.x * sinY + z1 * cosY,
  };
}

function project(point) {
  const rotated = rotatePoint(point);
  return {
    x: CENTER_X + rotated.x * SCALE,
    y: CENTER_Y - rotated.y * SCALE,
    z: rotated.z,
  };
}

function format(value) {
  return Number(value.toFixed(2));
}

function pathFromPoints(points, { close = false } = {}) {
  const commands = points.map((point, index) => {
    const projected = project(point);
    return `${index === 0 ? "M" : "L"} ${format(projected.x)} ${format(projected.y)}`;
  });
  if (close) commands.push("Z");
  return commands.join(" ");
}

function polygonMarkup() {
  const thetaSegments = 40;
  const latitudeSegments = 12;
  const cells = [];

  for (let latitudeIndex = 0; latitudeIndex < latitudeSegments; latitudeIndex += 1) {
    const latitudeA = -Math.PI / 2 + (latitudeIndex / latitudeSegments) * Math.PI;
    const latitudeB = -Math.PI / 2 + ((latitudeIndex + 1) / latitudeSegments) * Math.PI;
    for (let thetaIndex = 0; thetaIndex < thetaSegments; thetaIndex += 1) {
      const thetaA = (thetaIndex / thetaSegments) * Math.PI * 2;
      const thetaB = ((thetaIndex + 1) / thetaSegments) * Math.PI * 2;
      const points = [
        pointOnFourArmSurface(thetaA, latitudeA),
        pointOnFourArmSurface(thetaB, latitudeA),
        pointOnFourArmSurface(thetaB, latitudeB),
        pointOnFourArmSurface(thetaA, latitudeB),
      ];
      const depth = points.reduce((sum, point) => sum + rotatePoint(point).z, 0) / points.length;
      cells.push({ points, depth });
    }
  }

  return cells
    .sort((a, b) => a.depth - b.depth)
    .map(({ points, depth }) => {
      const opacity = 0.018 + ((depth + 0.9) / 1.8) * 0.028;
      return `<path d="${pathFromPoints(points, { close: true })}" fill="${LIGHT_BLUE}" fill-opacity="${format(opacity)}"/>`;
    })
    .join("");
}

function latitudeMarkup() {
  const lines = [];
  for (let index = -7; index <= 7; index += 1) {
    const latitude = (index / 8) * (Math.PI / 2);
    const points = [];
    for (let thetaIndex = 0; thetaIndex <= 96; thetaIndex += 1) {
      const theta = (thetaIndex / 96) * Math.PI * 2;
      points.push(pointOnFourArmSurface(theta, latitude));
    }
    const opacity = index === 0 ? 0.82 : 0.48 + (1 - Math.abs(index) / 8) * 0.12;
    lines.push(`<path d="${pathFromPoints(points)}" opacity="${format(opacity)}"/>`);
  }
  return lines.join("");
}

function longitudeMarkup() {
  const lines = [];
  for (let index = 0; index < 24; index += 1) {
    const theta = (index / 24) * Math.PI * 2;
    const points = [];
    for (let latitudeIndex = 0; latitudeIndex <= 48; latitudeIndex += 1) {
      const latitude = -Math.PI / 2 + (latitudeIndex / 48) * Math.PI;
      points.push(pointOnFourArmSurface(theta, latitude));
    }
    lines.push(`<path d="${pathFromPoints(points)}" opacity="0.56"/>`);
  }
  return lines.join("");
}

function pinchGuideMarkup() {
  const top = project({ x: 0, y: 0, z: 0.61 });
  const bottom = project({ x: 0, y: 0, z: -0.61 });
  const middleX = (top.x + bottom.x) / 2;
  const middleY = (top.y + bottom.y) / 2;
  return `
    <ellipse cx="${format(middleX)}" cy="${format(middleY)}" rx="15" ry="46"
      fill="none" stroke="${RED}" stroke-width="2.6" stroke-dasharray="7 6" opacity="0.95"/>
  `;
}

function fourLobeBodyMarkup() {
  return `
    <g>${polygonMarkup()}</g>
    <g fill="none" stroke="${BLUE}" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round">
      ${latitudeMarkup()}
      ${longitudeMarkup()}
    </g>
  `;
}

function generateHamiltonIveyFigure() {
  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${WIDTH}" height="${HEIGHT}" viewBox="0 0 ${WIDTH} ${HEIGHT}" role="img" aria-labelledby="title desc">
  <title id="title">Smooth four-arm Hamilton-Ivey pinching model</title>
  <desc id="desc">A round central body deformed into four smooth, rounded arms, shown as a blue wireframe.</desc>
  ${fourLobeBodyMarkup()}
  ${pinchGuideMarkup()}
</svg>
`;
}

function svgDocument({ width, height, title, description, content }) {
  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}" role="img" aria-labelledby="title desc">
  <title id="title">${title}</title>
  <desc id="desc">${description}</desc>
  ${content}
</svg>
`;
}

function createProjector({ centerX, centerY, scale, tilt = -0.22, rotation = 0 }) {
  const cosTilt = Math.cos(tilt);
  const sinTilt = Math.sin(tilt);
  const cosRotation = Math.cos(rotation);
  const sinRotation = Math.sin(rotation);

  return (point) => {
    const flatX = point.x;
    const flatY = point.y * cosTilt - point.z * sinTilt;
    const rotatedX = flatX * cosRotation - flatY * sinRotation;
    const rotatedY = flatX * sinRotation + flatY * cosRotation;
    return {
      x: centerX + rotatedX * scale,
      y: centerY - rotatedY * scale,
    };
  };
}

function projectedPath(points, projector, { close = false } = {}) {
  const commands = points.map((point, index) => {
    const projected = projector(point);
    return `${index === 0 ? "M" : "L"} ${format(projected.x)} ${format(projected.y)}`;
  });
  if (close) commands.push("Z");
  return commands.join(" ");
}

function lathePoint(profile, axis, u, theta) {
  const { axisValue, radius } = profile(u);
  if (axis === "horizontal") {
    return {
      x: axisValue,
      y: radius * Math.cos(theta),
      z: radius * Math.sin(theta),
    };
  }
  return {
    x: radius * Math.cos(theta),
    y: axisValue,
    z: radius * Math.sin(theta),
  };
}

function renderLathe({
  profile,
  projector,
  axis = "vertical",
  color = BLUE,
  fillColor = LIGHT_BLUE,
  ringCount = 8,
  meridianCount = 12,
  startBoundary = "strong",
  endBoundary = "strong",
}) {
  const sampleCount = 56;
  const positiveSide = [];
  const negativeSide = [];
  for (let index = 0; index <= sampleCount; index += 1) {
    const u = index / sampleCount;
    positiveSide.push(lathePoint(profile, axis, u, 0));
    negativeSide.unshift(lathePoint(profile, axis, u, Math.PI));
  }

  const fill = `<path d="${projectedPath([...positiveSide, ...negativeSide], projector, { close: true })}"
    fill="${fillColor}" fill-opacity="0.12"/>`;

  const meridians = [];
  for (let index = 0; index < meridianCount; index += 1) {
    const theta = (index / meridianCount) * Math.PI * 2;
    const points = [];
    for (let sample = 0; sample <= sampleCount; sample += 1) {
      points.push(lathePoint(profile, axis, sample / sampleCount, theta));
    }
    meridians.push(`<path d="${projectedPath(points, projector)}" opacity="0.62"/>`);
  }

  const rings = [];
  for (let index = 0; index <= ringCount; index += 1) {
    const u = index / ringCount;
    const { radius } = profile(u);
    if (radius < 0.008) continue;
    const points = [];
    for (let sample = 0; sample <= 64; sample += 1) {
      points.push(lathePoint(profile, axis, u, (sample / 64) * Math.PI * 2));
    }
    const boundary = index === 0 ? startBoundary : index === ringCount ? endBoundary : null;
    const strokeWidth = boundary === "strong" ? 2.6 : boundary === "soft" ? 1.05 : 1.35;
    const opacity = boundary === "strong" ? 0.94 : boundary === "soft" ? 0.3 : 0.68;
    rings.push(`<path d="${projectedPath(points, projector)}" stroke-width="${strokeWidth}"
      opacity="${opacity}"/>`);
  }

  return `
    ${fill}
    <g fill="none" stroke="${color}" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round">
      ${rings.join("")}
      ${meridians.join("")}
    </g>
  `;
}

function sphereProfile(u) {
  const axisValue = -1 + 2 * u;
  return {
    axisValue,
    radius: Math.sqrt(Math.max(0, 1 - axisValue * axisValue)),
  };
}

function smoothStep(value) {
  const clamped = Math.max(0, Math.min(1, value));
  return clamped * clamped * (3 - 2 * clamped);
}

function doubleArrowMarkup({ x1, y1, x2, y2, color = RED, dashed = true }) {
  const dx = x2 - x1;
  const dy = y2 - y1;
  const length = Math.hypot(dx, dy);
  const ux = dx / length;
  const uy = dy / length;
  const px = -uy;
  const py = ux;
  const headLength = 17;
  const headWidth = 8;
  const leftBaseX = x1 + ux * headLength;
  const leftBaseY = y1 + uy * headLength;
  const rightBaseX = x2 - ux * headLength;
  const rightBaseY = y2 - uy * headLength;
  return `
    <line x1="${format(leftBaseX)}" y1="${format(leftBaseY)}" x2="${format(rightBaseX)}" y2="${format(rightBaseY)}"
      stroke="${color}" stroke-width="3" ${dashed ? 'stroke-dasharray="8 6"' : ""}/>
    <path d="M ${format(x1)} ${format(y1)} L ${format(leftBaseX + px * headWidth)} ${format(leftBaseY + py * headWidth)}
      L ${format(leftBaseX - px * headWidth)} ${format(leftBaseY - py * headWidth)} Z" fill="${color}"/>
    <path d="M ${format(x2)} ${format(y2)} L ${format(rightBaseX + px * headWidth)} ${format(rightBaseY + py * headWidth)}
      L ${format(rightBaseX - px * headWidth)} ${format(rightBaseY - py * headWidth)} Z" fill="${color}"/>
  `;
}

function ellipsisMarkup(x, y, color = BLUE) {
  return [0, 1, 2]
    .map((index) => `<circle cx="${x + index * 18}" cy="${y}" r="4.2" fill="${color}" opacity="0.82"/>`)
    .join("");
}

function generateReducedVolumeFigure() {
  const profile = (u) => ({
    axisValue: 0.82 - 1.64 * u,
    radius: 0.29 + 0.49 * smoothStep(u),
  });
  const surface = renderLathe({
    profile,
    projector: createProjector({ centerX: 210, centerY: 150, scale: 118 }),
    ringCount: 8,
    meridianCount: 14,
  });
  return svgDocument({
    width: 420,
    height: 300,
    title: "Perelman reduced-volume tube",
    description: "A truncated tube with a small upper boundary, a larger lower boundary, and a double-ended arrow along its axis.",
    content: `${surface}${doubleArrowMarkup({ x1: 210, y1: 76, x2: 210, y2: 224 })}`,
  });
}

function generateKappaModelsFigure() {
  const neckProfile = (u) => ({
    axisValue: -0.78 + 1.56 * u,
    radius: 0.35 + 0.31 * Math.abs(2 * u - 1) ** 1.55,
  });
  const neck = renderLathe({
    profile: neckProfile,
    projector: createProjector({ centerX: 135, centerY: 130, scale: 92 }),
    ringCount: 8,
    meridianCount: 12,
  });
  const sphere = renderLathe({
    profile: sphereProfile,
    projector: createProjector({ centerX: 365, centerY: 130, scale: 72 }),
    ringCount: 9,
    meridianCount: 14,
  });
  return svgDocument({
    width: 600,
    height: 260,
    title: "Kappa-solution models",
    description: "A bounded neck model beside a round spherical model.",
    content: `${neck}${sphere}${ellipsisMarkup(485, 135)}`,
  });
}

function meltedSphereProfile(u) {
  const sphere = Math.sqrt(Math.max(0, 1 - (2 * u - 1) ** 2));
  const melt = 0.84 * smoothStep((u - 0.5) / 0.5);
  return {
    axisValue: 0.92 - 1.66 * u,
    radius: 0.72 * sphere + melt,
  };
}

function generateCanonicalFigure() {
  const cylinder = renderLathe({
    profile: (u) => ({ axisValue: -0.72 + 1.44 * u, radius: 0.54 }),
    projector: createProjector({ centerX: 105, centerY: 132, scale: 72 }),
    color: GREEN,
    fillColor: LIGHT_GREEN,
    ringCount: 7,
    meridianCount: 12,
  });
  const sphere = renderLathe({
    profile: sphereProfile,
    projector: createProjector({ centerX: 500, centerY: 132, scale: 62 }),
    ringCount: 8,
    meridianCount: 12,
  });
  const meltedSphere = renderLathe({
    profile: meltedSphereProfile,
    projector: createProjector({ centerX: 690, centerY: 137, scale: 62 }),
    ringCount: 8,
    meridianCount: 12,
    endBoundary: "soft",
  });
  const fourLobe = `<g transform="translate(305 132) scale(0.42) translate(-${CENTER_X} -${CENTER_Y})">
    ${fourLobeBodyMarkup()}
  </g>`;
  return svgDocument({
    width: 900,
    height: 270,
    title: "Canonical neighborhood models",
    description: "A closed cylinder, the smooth four-arm pinching model, a sphere, and a sphere melted into a flared lower cap.",
    content: `${cylinder}${fourLobe}${sphere}${meltedSphere}${ellipsisMarkup(810, 140)}`,
  });
}

function pinchedSphereProfile(waist) {
  return (u) => {
    const axisValue = -1 + 2 * u;
    const envelope = Math.sqrt(Math.max(0, 1 - axisValue * axisValue));
    const bulge = 1 - Math.exp(-Math.pow(Math.abs(axisValue) / 0.3, 2));
    return {
      axisValue,
      radius: envelope * (waist + (0.78 - waist) * bulge),
    };
  };
}

function scissorsMarkup(x, y) {
  return `
    <g fill="none" stroke="#17366f" stroke-width="2.4" stroke-linecap="round">
      <circle cx="${x - 7}" cy="${y + 7}" r="5"/><circle cx="${x + 7}" cy="${y + 7}" r="5"/>
      <path d="M ${x - 4} ${y + 3} L ${x + 13} ${y - 16} M ${x + 4} ${y + 3} L ${x - 13} ${y - 16}"/>
    </g>
  `;
}

function dashedForwardArrow(x1, x2, y) {
  return `
    <line x1="${x1}" y1="${y}" x2="${x2 - 12}" y2="${y}" stroke="${RED}" stroke-width="2.3" stroke-dasharray="7 6"/>
    <path d="M ${x2} ${y} L ${x2 - 13} ${y - 6} L ${x2 - 13} ${y + 6} Z" fill="${RED}"/>
  `;
}

function generateSurgeryFigure() {
  const centers = [110, 360, 610];
  const waists = [0.31, 0.44, 0.58];
  const surfaces = centers.map((centerX, index) => renderLathe({
    profile: pinchedSphereProfile(waists[index]),
    axis: "horizontal",
    projector: createProjector({ centerX, centerY: 116, scale: 88, rotation: index === 0 ? -0.1 : index === 2 ? 0.08 : 0 }),
    ringCount: 9,
    meridianCount: 12,
  })).join("");
  return svgDocument({
    width: 740,
    height: 250,
    title: "Ricci flow surgery sequence",
    description: "Three closed deformed spheres whose central neck becomes progressively less thin after controlled surgery.",
    content: `${surfaces}${dashedForwardArrow(205, 265, 116)}${dashedForwardArrow(455, 515, 116)}${scissorsMarkup(235, 202)}${scissorsMarkup(485, 202)}`,
  });
}

function gaussianProfile(u) {
  const tail = Math.exp(-1.7);
  const height = (Math.exp(-1.7 * u * u) - tail) / (1 - tail);
  return {
    axisValue: -0.35 + 0.9 * height,
    radius: 1.05 * u,
  };
}

function generateSurgeryControlFigure() {
  const gaussian = renderLathe({
    profile: gaussianProfile,
    projector: createProjector({ centerX: 130, centerY: 135, scale: 92 }),
    ringCount: 8,
    meridianCount: 14,
  });
  const sphere = renderLathe({
    profile: sphereProfile,
    projector: createProjector({ centerX: 390, centerY: 132, scale: 70 }),
    ringCount: 9,
    meridianCount: 14,
  });
  return svgDocument({
    width: 600,
    height: 260,
    title: "A priori surgery models",
    description: "A smooth Gaussian cap related by a double-ended arrow to a round sphere.",
    content: `${gaussian}${doubleArrowMarkup({ x1: 238, y1: 132, x2: 302, y2: 132, color: "#17366f", dashed: false })}${sphere}${ellipsisMarkup(505, 137)}`,
  });
}

function generateSphereFigure({
  title = "Round geometric model",
  description = "A round blue wireframe sphere.",
} = {}) {
  const sphere = renderLathe({
    profile: sphereProfile,
    projector: createProjector({ centerX: 210, centerY: 150, scale: 104 }),
    ringCount: 10,
    meridianCount: 16,
  });
  return svgDocument({ width: 420, height: 300, title, description, content: sphere });
}

function generateBallsFigure() {
  const specs = [
    [92, 48],
    [205, 39],
    [300, 29],
    [372, 18],
  ];
  const spheres = specs.map(([centerX, scale]) => renderLathe({
    profile: sphereProfile,
    projector: createProjector({ centerX, centerY: 132, scale }),
    ringCount: 7,
    meridianCount: 10,
  })).join("");
  return svgDocument({
    width: 560,
    height: 260,
    title: "Noncollapsing ball sequence",
    description: "A sequence of round balls at decreasing scales.",
    content: `${spheres}${ellipsisMarkup(430, 137)}`,
  });
}

function generateExtinctionFigure() {
  const specs = [
    [95, 50],
    [215, 39],
    [315, 27],
  ];
  const spheres = specs.map(([centerX, scale]) => renderLathe({
    profile: sphereProfile,
    projector: createProjector({ centerX, centerY: 132, scale }),
    ringCount: 7,
    meridianCount: 10,
  })).join("");
  return svgDocument({
    width: 560,
    height: 260,
    title: "Finite-time extinction sequence",
    description: "Round components shrink through time toward extinction.",
    content: `${spheres}${ellipsisMarkup(380, 137)}<text x="500" y="151" fill="#17366f" font-family="Georgia,serif" font-size="38" font-style="italic">t</text>`,
  });
}

function generateFinalSphereFigure() {
  return svgDocument({
    width: 420,
    height: 300,
    title: "Poincare conclusion",
    description: "A blue circular conclusion mark containing a check.",
    content: `
      <circle cx="210" cy="150" r="86" fill="#8eafe0" fill-opacity="0.08" stroke="#17366f" stroke-width="8"/>
      <path d="M 160 150 L 195 185 L 265 108" fill="none" stroke="#315da8" stroke-width="8"
        stroke-linecap="round" stroke-linejoin="round"/>
    `,
  });
}

await mkdir(outputDirectory, { recursive: true });
const figures = [
  ["pinch", generateHamiltonIveyFigure()],
  ["hourglass", generateReducedVolumeFigure()],
  ["models", generateKappaModelsFigure()],
  ["canonical", generateCanonicalFigure()],
  ["surgery", generateSurgeryFigure()],
  ["cap", generateSurgeryControlFigure()],
  ["sphere", generateSphereFigure()],
  ["balls", generateBallsFigure()],
  ["extinction", generateExtinctionFigure()],
  ["spaceform", generateSphereFigure({ title: "Spherical space-form model" })],
  ["final-sphere", generateFinalSphereFigure()],
];
await Promise.all(figures.map(([name, content]) => writeFile(`${outputDirectory}/${name}.svg`, content)));
console.log(`Generated ${figures.map(([name]) => `public/figures/${name}.svg`).join(", ")}`);
