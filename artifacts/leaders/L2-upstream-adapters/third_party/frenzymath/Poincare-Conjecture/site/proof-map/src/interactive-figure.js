import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";

const COLORS = {
  blue: 0x315da8,
  blueLight: 0x8eafe0,
  green: 0x4e8a70,
  greenLight: 0xa9cdbb,
  red: 0xdf5d55,
  ink: 0x17366f,
};

function lineMaterial(color = COLORS.blue, opacity = 0.68) {
  return new THREE.LineBasicMaterial({
    color,
    transparent: true,
    opacity,
    depthWrite: false,
  });
}

function surfaceMaterial(color = COLORS.blueLight, opacity = 0.13) {
  return new THREE.MeshBasicMaterial({
    color,
    transparent: true,
    opacity,
    side: THREE.DoubleSide,
    depthWrite: false,
  });
}

function lathePoint(profile, axis, u, theta) {
  const { axisValue, radius } = profile(u);
  if (axis === "horizontal") {
    return new THREE.Vector3(axisValue, radius * Math.cos(theta), radius * Math.sin(theta));
  }
  return new THREE.Vector3(radius * Math.cos(theta), axisValue, radius * Math.sin(theta));
}

function latheSurface(profile, options = {}) {
  const axis = options.axis ?? "vertical";
  const segmentsU = options.segmentsU ?? 28;
  const segmentsTheta = options.segmentsTheta ?? 36;
  const color = options.color ?? COLORS.blue;
  const fill = options.fill ?? COLORS.blueLight;
  const group = new THREE.Group();
  const vertices = [];
  const indices = [];

  for (let i = 0; i <= segmentsU; i += 1) {
    const u = i / segmentsU;
    for (let j = 0; j <= segmentsTheta; j += 1) {
      const point = lathePoint(profile, axis, u, (j / segmentsTheta) * Math.PI * 2);
      vertices.push(point.x, point.y, point.z);
    }
  }

  for (let i = 0; i < segmentsU; i += 1) {
    for (let j = 0; j < segmentsTheta; j += 1) {
      const a = i * (segmentsTheta + 1) + j;
      const b = a + segmentsTheta + 1;
      indices.push(a, b, a + 1, b, b + 1, a + 1);
    }
  }

  const geometry = new THREE.BufferGeometry();
  geometry.setAttribute("position", new THREE.Float32BufferAttribute(vertices, 3));
  geometry.setIndex(indices);
  geometry.computeVertexNormals();
  group.add(new THREE.Mesh(geometry, surfaceMaterial(fill, options.opacity ?? 0.13)));

  for (let i = 0; i <= segmentsU; i += 2) {
    const u = i / segmentsU;
    if (profile(u).radius < 0.008) continue;
    const points = [];
    for (let j = 0; j < segmentsTheta; j += 1) {
      points.push(lathePoint(profile, axis, u, (j / segmentsTheta) * Math.PI * 2));
    }
    const boundary = i === 0 || i === segmentsU;
    group.add(new THREE.LineLoop(
      new THREE.BufferGeometry().setFromPoints(points),
      lineMaterial(color, boundary ? 0.96 : 0.64),
    ));
  }

  for (let j = 0; j < segmentsTheta; j += 3) {
    const points = [];
    for (let i = 0; i <= segmentsU; i += 1) {
      points.push(lathePoint(profile, axis, i / segmentsU, (j / segmentsTheta) * Math.PI * 2));
    }
    group.add(new THREE.Line(
      new THREE.BufferGeometry().setFromPoints(points),
      lineMaterial(color, 0.62),
    ));
  }

  return group;
}

function sphereProfile(u) {
  const axisValue = -1 + 2 * u;
  return {
    axisValue,
    radius: Math.sqrt(Math.max(0, 1 - axisValue * axisValue)),
  };
}

function sphere(radius = 1, options = {}) {
  const model = latheSurface(sphereProfile, options);
  model.scale.setScalar(radius);
  return model;
}

function smoothStep(value) {
  const clamped = Math.max(0, Math.min(1, value));
  return clamped * clamped * (3 - 2 * clamped);
}

function fourLobeRadius(theta) {
  const lobe = Math.abs(Math.cos(2 * (theta - Math.PI / 4))) ** 2.4;
  return 0.48 + 0.62 * lobe;
}

function fourLobePoint(theta, latitude) {
  const planarRadius = fourLobeRadius(theta) * Math.cos(latitude);
  const coreBias = 0.82 + 0.18 * Math.abs(Math.cos(2 * (theta - Math.PI / 4)));
  return new THREE.Vector3(
    planarRadius * Math.cos(theta),
    planarRadius * Math.sin(theta),
    0.58 * coreBias * Math.sin(latitude),
  );
}

function fourLobeSurface(options = {}) {
  const thetaSegments = 48;
  const latitudeSegments = 22;
  const group = new THREE.Group();
  const vertices = [];
  const indices = [];

  for (let i = 0; i <= latitudeSegments; i += 1) {
    const latitude = -Math.PI / 2 + (i / latitudeSegments) * Math.PI;
    for (let j = 0; j <= thetaSegments; j += 1) {
      const point = fourLobePoint((j / thetaSegments) * Math.PI * 2, latitude);
      vertices.push(point.x, point.y, point.z);
    }
  }
  for (let i = 0; i < latitudeSegments; i += 1) {
    for (let j = 0; j < thetaSegments; j += 1) {
      const a = i * (thetaSegments + 1) + j;
      const b = a + thetaSegments + 1;
      indices.push(a, b, a + 1, b, b + 1, a + 1);
    }
  }
  const geometry = new THREE.BufferGeometry();
  geometry.setAttribute("position", new THREE.Float32BufferAttribute(vertices, 3));
  geometry.setIndex(indices);
  geometry.computeVertexNormals();
  group.add(new THREE.Mesh(geometry, surfaceMaterial(options.fill ?? COLORS.blueLight, 0.13)));

  for (let i = -8; i <= 8; i += 1) {
    const latitude = (i / 9) * (Math.PI / 2);
    const points = [];
    for (let j = 0; j < thetaSegments; j += 1) {
      points.push(fourLobePoint((j / thetaSegments) * Math.PI * 2, latitude));
    }
    group.add(new THREE.LineLoop(
      new THREE.BufferGeometry().setFromPoints(points),
      lineMaterial(options.color ?? COLORS.blue, i === 0 ? 0.88 : 0.6),
    ));
  }
  for (let j = 0; j < 24; j += 1) {
    const theta = (j / 24) * Math.PI * 2;
    const points = [];
    for (let i = 0; i <= latitudeSegments; i += 1) {
      points.push(fourLobePoint(theta, -Math.PI / 2 + (i / latitudeSegments) * Math.PI));
    }
    group.add(new THREE.Line(
      new THREE.BufferGeometry().setFromPoints(points),
      lineMaterial(options.color ?? COLORS.blue, 0.58),
    ));
  }
  return group;
}

function dashedLoop(points, color = COLORS.red) {
  const line = new THREE.LineLoop(
    new THREE.BufferGeometry().setFromPoints(points),
    new THREE.LineDashedMaterial({ color, dashSize: 0.08, gapSize: 0.055 }),
  );
  line.computeLineDistances();
  return line;
}

function pinchGuide() {
  const points = [];
  for (let index = 0; index < 64; index += 1) {
    const theta = (index / 64) * Math.PI * 2;
    points.push(new THREE.Vector3(0, 0.42 * Math.cos(theta), 0.58 * Math.sin(theta)));
  }
  return dashedLoop(points);
}

function taperedTube() {
  return latheSurface((u) => ({
    axisValue: 0.82 - 1.64 * u,
    radius: 0.29 + 0.49 * smoothStep(u),
  }));
}

function boundedNeck() {
  return latheSurface((u) => ({
    axisValue: 0.78 - 1.56 * u,
    radius: 0.35 + 0.31 * Math.abs(2 * u - 1) ** 1.55,
  }));
}

function meltedSphere() {
  return latheSurface((u) => {
    const roundPart = Math.sqrt(Math.max(0, 1 - (2 * u - 1) ** 2));
    return {
      axisValue: 0.92 - 1.66 * u,
      radius: 0.72 * roundPart + 0.84 * smoothStep((u - 0.5) / 0.5),
    };
  });
}

function pinchedSphere(waist) {
  return latheSurface((u) => {
    const axisValue = -1 + 2 * u;
    const envelope = Math.sqrt(Math.max(0, 1 - axisValue * axisValue));
    const bulge = 1 - Math.exp(-Math.pow(Math.abs(axisValue) / 0.3, 2));
    return {
      axisValue,
      radius: envelope * (waist + (0.78 - waist) * bulge),
    };
  }, { axis: "horizontal" });
}

function gaussianCap() {
  const tail = Math.exp(-1.7);
  return latheSurface((u) => ({
    axisValue: -0.35 + 0.9 * ((Math.exp(-1.7 * u * u) - tail) / (1 - tail)),
    radius: 1.05 * u,
  }));
}

function ellipsis(x, color = COLORS.ink) {
  const group = new THREE.Group();
  for (let index = 0; index < 3; index += 1) {
    const dot = new THREE.Mesh(
      new THREE.SphereGeometry(0.045, 12, 8),
      new THREE.MeshBasicMaterial({ color }),
    );
    dot.position.x = x + index * 0.16;
    group.add(dot);
  }
  return group;
}

function doubleArrow(direction = "vertical", color = COLORS.red) {
  const group = new THREE.Group();
  const vector = direction === "vertical" ? new THREE.Vector3(0, 1, 0) : new THREE.Vector3(1, 0, 0);
  const reverse = vector.clone().multiplyScalar(-1);
  group.add(new THREE.ArrowHelper(vector, new THREE.Vector3(), 0.72, color, 0.14, 0.09));
  group.add(new THREE.ArrowHelper(reverse, new THREE.Vector3(), 0.72, color, 0.14, 0.09));
  return group;
}

function addAt(group, object, x, scale = 1) {
  object.position.x = x;
  object.scale.setScalar(scale);
  group.add(object);
  return object;
}

function buildVisual(kind) {
  const root = new THREE.Group();

  if (kind === "sphere" || kind === "spaceform") {
    root.add(sphere(0.92));
  } else if (kind === "final-sphere") {
    root.add(sphere(0.92, { color: COLORS.ink }));
  } else if (kind === "pinch") {
    root.add(fourLobeSurface(), pinchGuide());
  } else if (kind === "hourglass") {
    root.add(taperedTube(), doubleArrow());
  } else if (kind === "balls") {
    [[-1.05, 0.42], [-0.28, 0.34], [0.38, 0.25], [0.9, 0.16]].forEach(([x, scale]) => {
      addAt(root, sphere(1), x, scale);
    });
    root.add(ellipsis(1.18));
  } else if (kind === "models") {
    addAt(root, boundedNeck(), -0.9, 0.82);
    addAt(root, sphere(1), 0.55, 0.62);
    root.add(ellipsis(1.18));
  } else if (kind === "canonical") {
    const cylinder = latheSurface((u) => ({ axisValue: 0.72 - 1.44 * u, radius: 0.54 }), {
      color: COLORS.green,
      fill: COLORS.greenLight,
    });
    addAt(root, cylinder, -2.2, 0.68);
    addAt(root, fourLobeSurface(), -0.9, 0.5);
    addAt(root, sphere(1), 0.25, 0.56);
    addAt(root, meltedSphere(), 1.45, 0.58);
    root.add(ellipsis(2.05));
  } else if (kind === "surgery") {
    addAt(root, pinchedSphere(0.31), -1.75, 0.72);
    addAt(root, pinchedSphere(0.44), 0, 0.72);
    addAt(root, pinchedSphere(0.58), 1.75, 0.72);
  } else if (kind === "cap") {
    addAt(root, gaussianCap(), -0.95, 0.76);
    const arrow = doubleArrow("horizontal", COLORS.ink);
    arrow.position.x = 0.1;
    arrow.scale.setScalar(0.42);
    root.add(arrow);
    addAt(root, sphere(1), 1.1, 0.62);
    root.add(ellipsis(1.8));
  } else if (kind === "extinction") {
    addAt(root, sphere(1), -0.9, 0.5);
    addAt(root, sphere(1), 0, 0.36);
    addAt(root, sphere(1), 0.72, 0.23);
    root.add(ellipsis(1.15));
  }

  root.rotation.set(-0.1, -0.28, 0);
  return root;
}

function disposeScene(scene) {
  scene.traverse((object) => {
    object.geometry?.dispose?.();
    if (Array.isArray(object.material)) {
      object.material.forEach((material) => material.dispose?.());
    } else {
      object.material?.dispose?.();
    }
  });
}

export function mountInteractiveFigure(host, kind) {
  host.replaceChildren();
  const canvas = document.createElement("canvas");
  canvas.setAttribute("aria-label", "Interactive 3D geometric model");
  canvas.tabIndex = 0;
  host.append(canvas);

  let renderer;
  try {
    renderer = new THREE.WebGLRenderer({ canvas, alpha: true, antialias: true, powerPreference: "high-performance" });
  } catch {
    canvas.remove();
    return null;
  }
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.setClearColor(0xffffff, 0);
  renderer.outputColorSpace = THREE.SRGBColorSpace;

  const scene = new THREE.Scene();
  const root = buildVisual(kind);
  scene.add(root);
  const camera = new THREE.PerspectiveCamera(32, 1, 0.01, 100);
  const controls = new OrbitControls(camera, canvas);
  controls.enablePan = false;
  controls.enableDamping = false;

  const bounds = new THREE.Box3().setFromObject(root);
  const sphereBounds = bounds.getBoundingSphere(new THREE.Sphere());
  const radius = Math.max(0.8, sphereBounds.radius);
  const distance = (radius / Math.sin(THREE.MathUtils.degToRad(camera.fov) / 2)) * 1.08;
  camera.position.set(sphereBounds.center.x, sphereBounds.center.y + radius * 0.05, distance);
  camera.near = Math.max(0.01, distance - radius * 3);
  camera.far = distance + radius * 4;
  controls.target.copy(sphereBounds.center);
  controls.minDistance = Math.max(1.2, distance * 0.58);
  controls.maxDistance = distance * 2.2;
  controls.update();
  controls.saveState();

  function render() {
    const width = host.clientWidth;
    const height = host.clientHeight;
    if (!width || !height) return;
    const renderedWidth = canvas.width / renderer.getPixelRatio();
    const renderedHeight = canvas.height / renderer.getPixelRatio();
    if (renderedWidth !== width || renderedHeight !== height) {
      renderer.setSize(width, height, false);
      camera.aspect = width / height;
      camera.updateProjectionMatrix();
    }
    renderer.render(scene, camera);
  }

  controls.addEventListener("change", render);
  const resizeObserver = new ResizeObserver(render);
  resizeObserver.observe(host);
  render();

  return {
    reset() {
      controls.reset();
      render();
    },
    dispose() {
      resizeObserver.disconnect();
      controls.removeEventListener("change", render);
      controls.dispose();
      disposeScene(scene);
      renderer.dispose();
      renderer.forceContextLoss();
      host.replaceChildren();
    },
  };
}
